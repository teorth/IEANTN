"""A failed Git read is not an empty network baseline."""
import contextlib
import io
import subprocess
from test_ieantn import LITERATURE, FixtureRepo, bridged, ieantn, importing


class _DiffGit(FixtureRepo):
    def git(self, *args):
        return subprocess.run(
            ["git", "-c", "commit.gpgsign=false", *args],
            cwd=self.root, check=True, capture_output=True, text=True,
        )

    def setUp(self):
        super().setUp()
        self.git("init", "-q")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--allow-empty", "-m", "Empty base")

    def commit_all(self, message: str) -> None:
        self.git("add", "-A")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "-q", "-m", message)

    def report(self) -> str:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            result = ieantn.diff("HEAD")
        output.seek(0)
        text = output.getvalue()
        self._last_ok = result
        return text


class TestDiffBase(_DiffGit):
    def test_unknown_base_does_not_report_all_conclusions_as_new(self):
        self.write_node("A.v1", LITERATURE)
        output = io.StringIO()
        with contextlib.redirect_stdout(output), self.assertRaisesRegex(SystemExit, "cannot read network base"):
            ieantn.diff("missing-base")
        self.assertNotIn("new conclusion", output.getvalue())

    def test_valid_empty_base_is_still_supported(self):
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.diff("HEAD"))
        self.assertEqual(ieantn.state_at("HEAD")["conclusions"], {})


class TestBridgeLeafSet(_DiffGit):
    """A bridge may discharge assumptions. It may not acquire any.

    The leaf set is a property of the graph, so the check reads the committed yaml and the working
    tree and never asks Lean.
    """

    def test_a_bridge_that_acquires_an_assumption_fails(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        self.commit_all("base")
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Extra.v1"))
        self.write_node("A.v1", bridged("Mid.v1.main"))
        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("A.v1.main", text)
        self.assertIn("gained unproved assumptions", text)
        self.assertIn("Extra.v1.main", text)
        self.assertIn("Mid.v1.main", text)

    def test_an_acknowledgement_does_not_excuse_it(self) -> None:
        """The one `diff` error with no override, which is policy -- see docs/ROADMAP.md.

        Every other error is a conclusion edited in place, where a reviewer can weigh landing
        it against what it breaks. Here there is nothing to weigh: a restatement that rests on
        a new assumption is not a restatement, and the node should designate the weaker
        evidence it really has. An acknowledgement would record a bridge the network keeps
        trusting while knowing it transports less than it claims.
        """
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        self.commit_all("base")
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Extra.v1"))
        self.write_node("A.v1", bridged("Mid.v1.main"))
        changes = self.root / "changes"
        changes.mkdir()
        (changes / "bridge.yaml").write_text(
            "acknowledge:\n"
            "  - conclusion: A.v1.main\n"
            "    effect: receipt-voided\n"
            "    reason: >-\n"
            "      Acknowledging it must not help: this check has no override.\n",
            encoding="utf-8")
        # The acknowledgement is read -- an edit in place would be excused by it ...
        self.assertEqual(
            ieantn.acknowledged(),
            {"A.v1.main": "Acknowledging it must not help: this check has no override."})
        # ... and the leaf set still fails the branch.
        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("gained unproved assumptions", text)
        self.assertIn("does not cover", text)

    def test_discharging_an_assumption_is_a_note(self) -> None:
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Extra.v1"))
        self.write_node("A.v1", bridged("Mid.v1.main"))
        self.commit_all("base")
        self.write_node("A.v1", bridged("Extra.v1.main"))
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertIn("fewer unproved assumptions", text)
        self.assertIn("Mid.v1.main", text)
        self.assertNotIn("gained unproved assumptions", text)

    def test_an_unchanged_bridge_is_silent(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        self.commit_all("base")
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertNotIn("unproved assumptions", text)

    def test_a_new_bridged_conclusion_is_not_compared_to_nothing(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.commit_all("base")
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertIn("new conclusion `A.v1.main`", text)
        self.assertNotIn("gained unproved assumptions", text)

    def test_becoming_bridged_onto_a_new_leaf_fails(self) -> None:
        verified = LITERATURE.replace("kind: literature", "kind: lean-comparator")
        self.write_node("A.v1", verified)
        self.commit_all("base")
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("Leaf.v1.main", text)
        self.assertIn("gained unproved assumptions", text)

    def test_an_unbridged_import_is_not_this_check(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", importing("Leaf.v1"))
        self.commit_all("base")
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("A.v1", importing("Extra.v1"))
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertNotIn("gained unproved assumptions", text)
