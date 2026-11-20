"""Hypothesis names in a bridge are resolved in the enclosing namespace.

Lean tries `namespace ++ written` before the written name. A binder copied as text
therefore composes the wrong conclusion whenever the longer name exists, and a short
name such as `main` inside `B.v1` matches nothing.
"""
import contextlib
import io
import json
import unittest
import unittest.mock

from test_ieantn import LITERATURE, FixtureRepo, bridged, ieantn


def _decl() -> dict:
    line = "def main : Prop := True"
    return dict(
        module="IEANTN.Nodes.A.v1.Conclusions", name="A.v1.main",
        startLine=5, startCol=0, endLine=5, endCol=len(line),
        nameStartLine=5, nameStartCol=4, nameEndLine=5, nameEndCol=8,
    )


class TestBridgeBinderResolution(FixtureRepo):
    def spin(self, key: str = "A.v1.main") -> tuple[bool, str]:
        result = ieantn.subprocess.CompletedProcess(
            [], 0, json.dumps({"declarations": [_decl()]}), ""
        )
        output = io.StringIO()
        with unittest.mock.patch.object(ieantn, "receipt_state", return_value=None), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=result), \
             contextlib.redirect_stdout(output):
            ok = ieantn.spinoff(key, "export", False)
        return ok, output.getvalue()

    def test_a_shadowed_binder_uses_the_enclosing_namespace(self) -> None:
        text = (
            "namespace Demo\n"
            "-- λ\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        found = ieantn.bridge_theorems(
            text, "A.v1.main", {"A.v1.main", "B.v1.main", "Demo.B.v1.main"}
        )
        self.assertEqual(found, [("Demo.from_b", ["Demo.B.v1.main"])])

    def test_a_short_binder_is_prefixed_with_the_enclosing_namespace(self) -> None:
        text = (
            "namespace B.v1\n"
            "theorem to_a (h : main) : A.v1.main := trivial\n"
            "end B.v1\n"
        )
        found = ieantn.bridge_theorems(text, "A.v1.main", {"A.v1.main", "B.v1.main"})
        self.assertEqual(found, [("B.v1.to_a", ["B.v1.main"])])

    def test_a_root_binder_stays_root_when_no_longer_name_exists(self) -> None:
        text = (
            "namespace Demo\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        found = ieantn.bridge_theorems(text, "A.v1.main", {"A.v1.main", "B.v1.main"})
        self.assertEqual(found, [("Demo.from_b", ["B.v1.main"])])

    def test_composition_applies_the_shadowed_hypothesis(self) -> None:
        self.write_node("B.v1", LITERATURE)
        self.write_node("Demo.B.v1", LITERATURE)
        body = bridged("Demo.B.v1.main").replace(
            "bridge: IEANTN/Bridges/a.lean",
            "bridge: IEANTN/Bridges/Demo/FromB.lean",
        )
        self.write_node("A.v1", body)
        bridge = self.root / "IEANTN" / "Bridges" / "Demo" / "FromB.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text(
            "namespace Demo\n"
            "-- the λ in this comment must survive a UTF-8 round trip\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n",
            encoding="utf-8",
        )
        ok, text = self.spin()
        self.assertTrue(ok, text)
        solution = (self.root / "export" / "Solution.lean").read_text(encoding="utf-8")
        self.assertIn("(Demo.from_b demo_b_v1_main)", solution)
        self.assertNotIn("(Demo.from_b b_v1_main)", solution)

    def test_a_short_binder_composes_through_the_bridge_under_it(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("B.v1", bridged("Leaf.v1.main"))
        body = bridged("B.v1.main").replace(
            "bridge: IEANTN/Bridges/a.lean",
            "bridge: IEANTN/Bridges/A/ToA.lean",
        )
        self.write_node("A.v1", body)
        (self.root / "IEANTN" / "Bridges").mkdir(parents=True, exist_ok=True)
        (self.root / "IEANTN" / "Bridges" / "a.lean").write_text(
            "theorem to_b (h : Leaf.v1.main) : B.v1.main := trivial\n",
            encoding="utf-8",
        )
        nested = self.root / "IEANTN" / "Bridges" / "A" / "ToA.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text(
            "namespace B.v1\n"
            "-- λ\n"
            "theorem to_a (h : main) : A.v1.main := trivial\n"
            "end B.v1\n",
            encoding="utf-8",
        )
        ok, text = self.spin()
        self.assertTrue(ok, text)
        solution = (self.root / "export" / "Solution.lean").read_text(encoding="utf-8")
        self.assertIn("(B.v1.to_a (to_b leaf_v1_main))", solution)


if __name__ == "__main__":
    unittest.main()
