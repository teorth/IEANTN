"""Narrow bridge applications: one explicit theorem, no guessed proof."""

from __future__ import annotations

import importlib.util
import io
import pathlib
import unittest
from contextlib import redirect_stderr, redirect_stdout


def load():
    path = pathlib.Path(__file__).resolve().parent.parent / "scripts" / "bridge_application.py"
    spec = importlib.util.spec_from_file_location("bridge_application", path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


bridge = load()


class DescribeBridgeTest(unittest.TestCase):
    def test_namespace_and_full_name_are_the_same_application(self) -> None:
        known = {"True"}
        namespace = bridge.describe_bridge(bridge.NAMESPACE_SPELLING, "True", known)
        full = bridge.describe_bridge(bridge.FULL_NAME_SPELLING, "True", known)
        self.assertEqual(namespace, full)
        self.assertEqual(namespace.full_name, "Demo.from_b")
        self.assertEqual(namespace.conclusion, "True")
        self.assertEqual([(item.name, item.binder_type) for item in namespace.premises], [("h", "True")])

    def test_nested_namespace_is_prefixed(self) -> None:
        text = (
            "namespace Outer.Inner\n"
            "theorem step (h : B.v1.main) (k : C.v1.main) :\n  A.v1.main := h\n"
            "end Outer.Inner\n"
        )
        found = bridge.describe_bridge(text, "A.v1.main", {"B.v1.main", "C.v1.main"})
        self.assertEqual(found.full_name, "Outer.Inner.step")
        self.assertEqual([item.binder_type for item in found.premises], ["B.v1.main", "C.v1.main"])

    def test_ambiguous_dotted_name_inside_a_namespace_is_rejected(self) -> None:
        text = "namespace Demo\ntheorem Demo.from_b (h : True) : True := h\nend Demo\n"
        with self.assertRaises(bridge.BridgeDescriptionError) as caught:
            bridge.describe_bridge(text, "True", {"True"})
        self.assertIn("ambiguous dotted name", str(caught.exception))

    def test_dotted_name_with_a_different_conclusion_does_not_hide_the_match(self) -> None:
        text = (
            "namespace Demo\n"
            "theorem Demo.other (h : True) : False := h\n"
            "theorem from_b (h : True) : True := h\n"
            "end Demo\n"
        )
        found = bridge.describe_bridge(text, "True", {"True"})
        self.assertEqual(found.full_name, "Demo.from_b")

    def test_implicit_and_instance_binders_are_rejected(self) -> None:
        for binder in ("{h : True}", "⦃h : True⦄", "[h : True]"):
            text = f"theorem from_b {binder} : True := trivial\n"
            with self.assertRaises(bridge.BridgeDescriptionError) as caught:
                bridge.describe_bridge(text, "True", {"True"})
            self.assertIn("implicit binder", str(caught.exception))

    def test_an_implicit_match_is_not_saved_by_another_theorem(self) -> None:
        text = "theorem bad {h : True} : True := trivial\ntheorem good (h : True) : True := h\n"
        with self.assertRaises(bridge.BridgeDescriptionError) as caught:
            bridge.describe_bridge(text, "True", {"True"})
        self.assertIn("implicit binder", str(caught.exception))

    def test_two_matching_theorems_are_rejected(self) -> None:
        text = (
            "theorem one (h : True) : True := h\n"
            "theorem two (k : True) : True := k\n"
        )
        with self.assertRaises(bridge.BridgeDescriptionError) as caught:
            bridge.describe_bridge(text, "True", {"True"})
        message = str(caught.exception)
        self.assertIn("two theorems match", message)
        self.assertIn("`one`", message)
        self.assertIn("`two`", message)
        self.assertIn("Refusing to guess", message)

    def test_a_side_condition_does_not_count_as_a_second_match(self) -> None:
        text = (
            "namespace Demo\n"
            "theorem side (h : B.v1.main) (n : Nat) : A.v1.main := h\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := h\n"
            "end Demo\n"
        )
        found = bridge.describe_bridge(text, "A.v1.main", {"B.v1.main"})
        self.assertEqual(found.full_name, "Demo.from_b")
        self.assertEqual([item.binder_type for item in found.premises], ["B.v1.main"])

    def test_a_commented_duplicate_is_not_a_second_theorem(self) -> None:
        text = (
            "namespace Demo\n"
            "theorem from_b (h : True) : True := h\n"
            "/- theorem other (h : True) : True := h -/\n"
            "-- theorem third (h : True) : True := h\n"
            "end Demo\n"
        )
        found = bridge.describe_bridge(text, "True", {"True"})
        self.assertEqual(found.full_name, "Demo.from_b")

    def test_grouped_binder_names_are_not_a_narrow_premise(self) -> None:
        text = "theorem from_b (h k : True) : True := h\n"
        with self.assertRaises(bridge.BridgeDescriptionError) as caught:
            bridge.describe_bridge(text, "True", {"True"})
        self.assertIn("explicit", str(caught.exception))

    def test_format_does_not_claim_a_proof(self) -> None:
        application = bridge.describe_bridge(bridge.NAMESPACE_SPELLING, "True", {"True"})
        text = bridge.format_application(application)
        self.assertIn("does not claim a proof", text)
        self.assertNotIn("proved", text)


class EquivalentSpellingTest(unittest.TestCase):
    def test_the_combined_file_has_both_spellings_and_they_agree(self) -> None:
        source = bridge.equivalent_spelling_file()
        self.assertNotIn("import Mathlib", source)
        self.assertIn("namespace Demo", source)
        self.assertIn("theorem Demo.from_b", source)
        checked = bridge.check_equivalent_spellings(source)
        self.assertEqual(checked.application.full_name, "Demo.from_b")
        self.assertIn(checked.lean, {"checked", "skipped"})
        if checked.lean == "skipped":
            self.assertTrue(checked.detail)

    def test_concatenating_the_spellings_is_two_matches(self) -> None:
        both = bridge.NAMESPACE_SPELLING + bridge.FULL_NAME_SPELLING
        with self.assertRaises(bridge.BridgeDescriptionError) as caught:
            bridge.describe_bridge(both, "True", {"True"})
        self.assertIn("two theorems match", str(caught.exception))


class CommandLineTest(unittest.TestCase):
    def test_describe_command_prints_the_application(self) -> None:
        with io.StringIO() as stdout, io.StringIO() as stderr:
            with redirect_stdout(stdout), redirect_stderr(stderr):
                code = bridge.main(
                    ["describe", str(_write_sample(self)), "--target", "True", "--known", "True"]
                )
            self.assertEqual(code, 0, stderr.getvalue())
            text = stdout.getvalue()
        self.assertIn("full_name: Demo.from_b", text)
        self.assertIn("does not claim a proof", text)

    def test_check_equivalent_command(self) -> None:
        with io.StringIO() as stdout, io.StringIO() as stderr:
            with redirect_stdout(stdout), redirect_stderr(stderr):
                code = bridge.main(["check-equivalent"])
            self.assertEqual(code, 0, stderr.getvalue())
            text = stdout.getvalue()
        self.assertIn("spellings: identical", text)
        self.assertIn("lean: ", text)
        self.assertIn("does not claim a proof", text)


def _write_sample(test: unittest.TestCase) -> pathlib.Path:
    directory = pathlib.Path(test.id().replace(".", "_"))
    # Keep the sample next to the test process's temp via unittest's default tmp? Use the home
    # of the module under a directory the test removes.
    root = pathlib.Path(__file__).resolve().parent / "_bridge_cli_sample"
    root.mkdir(exist_ok=True)
    path = root / "Sample.lean"
    path.write_text(bridge.NAMESPACE_SPELLING, encoding="utf-8")
    test.addCleanup(lambda: path.unlink(missing_ok=True))
    test.addCleanup(lambda: root.rmdir() if root.exists() else None)
    del directory
    return path


if __name__ == "__main__":
    unittest.main()
