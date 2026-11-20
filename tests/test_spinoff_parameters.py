"""Section variables survive a spin-off.

`ieantn_spinoff` reports the elaborated telescope. The declaration range does not
include a surrounding `variable`, so the slice has to put that prefix back.
"""
import json
import unittest
import unittest.mock

from test_ieantn import LITERATURE, FixtureRepo, ieantn


def _decl(line: str, parameters: list) -> dict:
    name = "main"
    return dict(
        module="IEANTN.Nodes.A.v1.Conclusions",
        name="A.v1.main",
        parameters=parameters,
        startLine=1,
        startCol=0,
        endLine=1,
        endCol=len(line),
        nameStartLine=1,
        nameStartCol=line.index(name),
        nameEndLine=1,
        nameEndCol=line.index(name) + len(name),
    )


class TestSpinoffParameters(FixtureRepo):
    def test_section_variable_is_reinserted_in_the_challenge(self) -> None:
        self.write_node("A.v1", LITERATURE)
        nodes = ieantn.load_nodes()
        nodes["A.v1"]["conclusions"][0]["justifications"][0]["kind"] = "lean-comparator"
        solution = self.root / "Solutions" / "A.v1"
        solution.mkdir(parents=True)
        (solution / "Solution.lean").write_text(
            "theorem A.v1.challenge_main : A.v1.main := trivial\n", encoding="utf-8"
        )
        line = "def main : Prop := True"
        source = self.root / "IEANTN" / "Nodes" / "A" / "v1" / "Conclusions.lean"
        source.write_text(line + "\n", encoding="utf-8")
        parameters = [
            {"name": "c", "binder": "explicit", "type": "ℕ"},
            {"name": "inst", "binder": "instImplicit", "type": "NeZero c"},
        ]
        payload = json.dumps({"declarations": [_decl(line, parameters)]})
        result = ieantn.subprocess.CompletedProcess([], 0, payload, "")
        with unittest.mock.patch.object(ieantn, "load_nodes", return_value=nodes), \
             unittest.mock.patch.object(ieantn, "receipt_state", return_value=None), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=result):
            self.assertTrue(ieantn.spinoff("A.v1.main", "export", False))
        challenge = self.root / "export" / "Challenge.lean"
        text = challenge.read_text(encoding="utf-8")
        self.assertIn("def main (c : ℕ) [NeZero c] : Prop := True", text)
        self.assertIn("ℕ".encode("utf-8"), challenge.read_bytes())

    def test_a_binder_already_in_the_header_is_not_repeated(self) -> None:
        line = "def main (x : Nat) : Prop := True"
        decl = _decl(line, [
            {"name": "c", "binder": "explicit", "type": "ℕ"},
            {"name": "x", "binder": "explicit", "type": "Nat"},
        ])
        body, _ = ieantn.slice_source(line, decl, "")
        self.assertEqual(body, "def main (c : ℕ) (x : Nat) : Prop := True")

    def test_an_instance_already_written_stops_the_prefix(self) -> None:
        line = "noncomputable def main [NeZero c] : Nat := 0"
        decl = _decl(line, [
            {"name": "inst", "binder": "instImplicit", "type": "NeZero c"},
            {"name": "c", "binder": "explicit", "type": "ℕ"},
        ])
        # The declared name is `main`, which is not at the same columns as a plain `def`.
        decl["nameStartCol"] = line.index("main")
        decl["nameEndCol"] = decl["nameStartCol"] + 4
        decl["endCol"] = len(line)
        body, _ = ieantn.slice_source(line, decl, "")
        self.assertEqual(body, line)


if __name__ == "__main__":
    unittest.main()
