"""One-level spinoff must apply challenge arguments in yaml import order."""
import contextlib
import io
import json
import unittest.mock

from test_ieantn import LITERATURE, FixtureRepo, ieantn


def _decl() -> dict:
    line = "def main : Prop := True"
    return dict(
        module="IEANTN.Nodes.A.v1.Conclusions", name="A.v1.main",
        startLine=5, startCol=0, endLine=5, endCol=len(line),
        nameStartLine=5, nameStartCol=4, nameEndLine=5, nameEndCol=8,
    )


VERIFIED = """
- id: main
  declaration: {node}.main
  challenge: {node}.challenge_main
  imports:
    - node: Z.v1
      conclusion: main
    - node: A.v1
      conclusion: main
  justifications:
    - id: checked
      kind: lean-comparator
  designated: checked
"""


class TestSpinoffArgumentOrder(FixtureRepo):
    def test_one_level_challenge_keeps_yaml_binder_order(self) -> None:
        self.write_node("Z.v1", LITERATURE)
        self.write_node("A.v1", LITERATURE)
        self.write_node("Mid.v1", VERIFIED)
        solution = self.root / "Solutions" / "Mid.v1"
        solution.mkdir(parents=True)
        (solution / "Solution.lean").write_text(
            "theorem Mid.v1.challenge_main : Mid.v1.main := trivial\n",
            encoding="utf-8",
        )
        result = ieantn.subprocess.CompletedProcess(
            [], 0, json.dumps({"declarations": [_decl()]}), "")
        output = io.StringIO()
        with unittest.mock.patch.object(ieantn, "receipt_state", return_value=None), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=result), \
             contextlib.redirect_stdout(output):
            ok = ieantn.spinoff("Mid.v1.main", "export", False)
        self.assertTrue(ok, output.getvalue())
        text = (self.root / "export" / "Solution.lean").read_text(encoding="utf-8")
        self.assertIn("Mid.v1.challenge_main z_v1_main a_v1_main", text)
        self.assertNotIn("Mid.v1.challenge_main a_v1_main z_v1_main", text)
