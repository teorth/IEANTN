"""Regression coverage for the assembled Palomar module layout."""
import contextlib
import io
import json
import unittest
import unittest.mock
from test_ieantn import LITERATURE, FixtureRepo, bridged, ieantn, importing


class TestSpinoffLayout(FixtureRepo):
    def emit(self, global_name=False):
        self.write_node("A.v1", LITERATURE)
        nodes = ieantn.load_nodes()
        nodes["A.v1"]["conclusions"][0]["justifications"][0]["kind"] = "lean-comparator"
        solution = self.root / "Solutions" / "A.v1"
        solution.mkdir(parents=True)
        (solution / "Solution.lean").write_text("import Helper\ntheorem A.v1.challenge_main : A.v1.main := trivial\n")
        (solution / "Helper.lean").write_text("import IEANTN.Nodes.A.v1.Conclusions\n")
        source = self.root / "IEANTN" / "Nodes" / "A" / "v1" / "Conclusions.lean"
        name = "A.v1.main" if global_name else "main"
        source.write_text(f"import Mathlib\ndef {name} : Prop := True\n")
        decl = dict(module="IEANTN.Nodes.A.v1.Conclusions", name="A.v1.main",
                    startLine=2, startCol=0, endLine=2, endCol=len(f"def {name} : Prop := True"),
                    nameStartLine=2, nameStartCol=4, nameEndLine=2, nameEndCol=4 + len(name))
        result = ieantn.subprocess.CompletedProcess([], 0, json.dumps({"declarations": [decl]}), "")
        # The layout is what is under test, not the receipt: these fixtures designate
        # `lean-comparator` without a receipt file, which `spinoff` otherwise refuses.
        with unittest.mock.patch.object(ieantn, "load_nodes", return_value=nodes), \
             unittest.mock.patch.object(ieantn, "receipt_state", return_value=None), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=result):
            self.assertTrue(ieantn.spinoff("A.v1.main", "export", False))
        return self.root / "export"

    def test_wrapper_imports_vendored_proof_without_importing_itself(self):
        target = self.emit()
        imports = ieantn.imports_of(target / "Solution.lean")
        self.assertEqual(imports, ["Helper", "NodeSolution"])
        self.assertIn("theorem A.v1.challenge_main", (target / "NodeSolution.lean").read_text())
        self.assertIn("namespace A.v1\n", (target / "Challenge.lean").read_text())
        self.assertIn("end A.v1\n", (target / "Challenge.lean").read_text())

    def test_fully_qualified_definition_does_not_emit_unmatched_end(self):
        target = self.emit(global_name=True)
        challenge = (target / "Challenge.lean").read_text()
        self.assertNotIn("\nend ", challenge)
        self.assertIn("def A.v1.main : Prop := True", challenge)


def _decl() -> dict:
    line = "def main : Prop := True"
    return dict(
        module="IEANTN.Nodes.A.v1.Conclusions", name="A.v1.main",
        startLine=5, startCol=0, endLine=5, endCol=len(line),
        nameStartLine=5, nameStartCol=4, nameEndLine=5, nameEndCol=8,
    )


class TestComposition(FixtureRepo):
    """A spin-off whose hypotheses are not direct imports has to compose the path."""

    def spin(self, key: str = "A.v1.main") -> tuple[bool, str]:
        result = ieantn.subprocess.CompletedProcess([], 0, json.dumps({"declarations": [_decl()]}), "")
        output = io.StringIO()
        with unittest.mock.patch.object(ieantn, "receipt_state", return_value=None), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=result), \
             contextlib.redirect_stdout(output):
            ok = ieantn.spinoff(key, "export", False)
        return ok, output.getvalue()

    def put_solution(self, node_id: str, text: str, helper: str | None = None) -> None:
        directory = self.root / "Solutions" / node_id
        directory.mkdir(parents=True)
        (directory / "Solution.lean").write_text(text, encoding="utf-8")
        if helper is not None:
            (directory / "Helper.lean").write_text(helper, encoding="utf-8")

    def test_two_verified_steps_compose_and_vendor_under_their_nodes(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("B.v1", importing("Leaf.v1").replace("kind: none-yet", "kind: lean-comparator"))
        self.write_node("A.v1", importing("B.v1").replace("kind: none-yet", "kind: lean-comparator"))
        self.put_solution("A.v1", "import Helper\ntheorem A.v1.challenge_main : A.v1.main := trivial\n",
                          "import IEANTN\n")
        self.put_solution("B.v1", "theorem B.v1.challenge_main : B.v1.main := trivial\n")
        ok, text = self.spin()
        self.assertTrue(ok, text)
        solution = (self.root / "export" / "Solution.lean").read_text(encoding="utf-8")
        self.assertIn("(A.v1.challenge_main (B.v1.challenge_main leaf_v1_main))", solution)
        self.assertIn("import vendored.A.v1.NodeSolution", solution)
        self.assertIn("import vendored.B.v1.NodeSolution", solution)
        vendored = (self.root / "export" / "vendored" / "A" / "v1" / "NodeSolution.lean").read_text(encoding="utf-8")
        self.assertIn("import vendored.A.v1.Helper", vendored)
        self.assertNotIn("\nimport Helper\n", vendored)
        challenge = (self.root / "export" / "Challenge.lean").read_text(encoding="utf-8")
        self.assertIn("leaf_v1_main : Leaf.v1.main", challenge)
        self.assertNotIn("b_v1_main", challenge)
        self.assertIn("- Leaf.v1.main", text)
        self.assertFalse((self.root / "export" / "lakefile.toml").exists())

    def test_a_citation_in_the_middle_is_refused(self) -> None:
        self.write_node("Other.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Other.v1"))
        self.write_node("A.v1", importing("Mid.v1").replace("kind: none-yet", "kind: lean-comparator"))
        self.put_solution("A.v1", "theorem A.v1.challenge_main : A.v1.main := trivial\n")
        ok, text = self.spin()
        self.assertFalse(ok)
        self.assertIn("Mid.v1.main", text)
        self.assertIn("gap in the proof", text)
        self.assertFalse((self.root / "export").exists())

    def test_a_bridge_is_applied_by_the_theorem_that_states_the_conclusion(self) -> None:
        self.write_node("B.v1", LITERATURE.replace("kind: literature", "kind: lean-comparator"))
        body = bridged("B.v1.main").replace(
            "bridge: IEANTN/Bridges/a.lean",
            "bridge: IEANTN/Bridges/A/FromB.lean",
        )
        self.write_node("A.v1", body)
        bridge = self.root / "IEANTN" / "Bridges" / "A" / "FromB.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text(
            "namespace Demo\ntheorem from_b (h : B.v1.main) : A.v1.main := trivial\nend Demo\n",
            encoding="utf-8",
        )
        self.put_solution("B.v1", "theorem B.v1.challenge_main : B.v1.main := trivial\n")
        ok, text = self.spin()
        self.assertTrue(ok, text)
        solution = (self.root / "export" / "Solution.lean").read_text(encoding="utf-8")
        self.assertIn("(Demo.from_b B.v1.challenge_main)", solution)
        self.assertIn("import IEANTN.Bridges.A.FromB", solution)
        self.assertIn("import vendored.B.v1.NodeSolution", solution)

    def test_a_bridge_with_no_matching_theorem_is_refused(self) -> None:
        self.write_node("B.v1", LITERATURE.replace("kind: literature", "kind: lean-comparator"))
        body = bridged("B.v1.main").replace(
            "bridge: IEANTN/Bridges/a.lean",
            "bridge: IEANTN/Bridges/A/FromB.lean",
        )
        self.write_node("A.v1", body)
        bridge = self.root / "IEANTN" / "Bridges" / "A" / "FromB.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text("theorem unrelated : True := trivial\n", encoding="utf-8")
        self.put_solution("B.v1", "theorem B.v1.challenge_main : B.v1.main := trivial\n")
        ok, text = self.spin()
        self.assertFalse(ok)
        self.assertIn("Refusing to guess", text)


class TestBridgeTheorems(unittest.TestCase):
    def test_a_namespaced_theorem_is_prefixed_and_a_side_condition_is_not(self) -> None:
        text = (
            "namespace Demo\n"
            "theorem side (h : B.v1.main) (n : Nat) : A.v1.main := trivial\n"
            "theorem from_b (h : B.v1.main) :\n  A.v1.main := trivial\n"
            "end Demo\n"
        )
        found = ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"})
        self.assertEqual(found, [("Demo.from_b", ["B.v1.main"])])
