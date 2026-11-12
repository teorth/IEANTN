"""Pinned Palomar project files from an explicit plan. Lake is not run."""

from __future__ import annotations

import importlib.util
import io
import json
import pathlib
import re
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

import yaml


def load():
    path = pathlib.Path(__file__).resolve().parent.parent / "scripts" / "palomar_project.py"
    spec = importlib.util.spec_from_file_location("palomar_project", path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


project = load()
SHA = "d60421f10c16f5f6c2cb75f1067a72e24e616391"
PLAN = {
    "conclusion": "A.v1.main",
    "leaves": ["Leaf.v1.main", "Other.v1.main"],
}


def metadata(**overrides: str) -> dict[str, str]:
    fields = {
        "core_commit": SHA,
        "author": "Ada Lovelace",
        "source_url": "https://example.invalid/IEANTN",
        "licence": "Apache-2.0",
        "review_status": "unreviewed",
    }
    fields.update(overrides)
    return fields


class WriteProjectTest(unittest.TestCase):
    def test_writes_the_pin_the_skeleton_and_the_limitation_lines(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp)
            report = project.write_project(out, PLAN, metadata())
            lakefile = (out / "lakefile.toml").read_text(encoding="utf-8")
            form = yaml.safe_load((out / "formalization.yaml").read_text(encoding="utf-8"))
        self.assertIn(f'rev = "{SHA}"', lakefile)
        self.assertIn('git = "https://example.invalid/IEANTN"', lakefile)
        self.assertNotIn("lake-manifest", lakefile)
        self.assertEqual(form["pin"]["core_commit"], SHA)
        self.assertEqual(form["project"]["authors"], ["Ada Lovelace"])
        self.assertEqual(form["project"]["license"], "Apache-2.0")
        self.assertEqual(form["review"]["status"], "unreviewed")
        self.assertEqual(form["sources"][0]["url"], "https://example.invalid/IEANTN")
        self.assertNotIn("node", form)
        self.assertNotIn("conclusions", form)
        self.assertEqual(
            form["limitations"],
            [project.limitation_sentence(leaf) for leaf in PLAN["leaves"]],
        )
        self.assertIn("still to do by hand, and deliberately not guessed at:", report)
        self.assertIn("lake-manifest.json -- commit the one Lake resolves", report)
        for line in project.limitation_lines(PLAN["leaves"]):
            self.assertIn(line, report)
        self.assertIn("No commit SHA was invented.", report)
        self.assertNotIn("scientific claim is", form["project"]["description"])
        self.assertIn("does not add a scientific claim", form["project"]["description"])

    def test_missing_fields_write_nothing(self) -> None:
        fields = metadata()
        for key in ("core_commit", "author", "source_url", "licence", "review_status"):
            broken = dict(fields)
            broken.pop(key)
            with tempfile.TemporaryDirectory() as tmp:
                out = pathlib.Path(tmp) / "export"
                with self.assertRaises(project.PalomarExportError) as caught:
                    project.write_project(out, PLAN, broken)
                self.assertIn(key, str(caught.exception))
                self.assertFalse((out / "lakefile.toml").exists())
                self.assertFalse((out / "formalization.yaml").exists())

    def test_a_short_or_branch_pin_is_not_resolved(self) -> None:
        for commit in ("d60421f", "main", "HEAD", SHA[:-1] + "g"):
            with tempfile.TemporaryDirectory() as tmp:
                with self.assertRaises(project.PalomarExportError) as caught:
                    project.write_project(pathlib.Path(tmp), PLAN, metadata(core_commit=commit))
            self.assertIn("refusing to invent a commit SHA", str(caught.exception))

    def test_empty_leaves_use_the_spinoff_sentence_and_claim_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp)
            report = project.write_project(out, {"conclusion": "A.v1.main", "leaves": []}, metadata())
            form = yaml.safe_load((out / "formalization.yaml").read_text(encoding="utf-8"))
        self.assertIn("there are no hypotheses to name in the limitations", report)
        self.assertIn("there are no hypotheses to name in the limitations", form["limitations"])
        self.assertIn("does not claim the conclusion is proved", " ".join(form["limitations"]))
        self.assertFalse((out / "lake-manifest.json").exists())

    def test_the_writer_does_not_call_lake(self) -> None:
        source = pathlib.Path(project.__file__).read_text(encoding="utf-8")
        self.assertNotIn("subprocess", source)
        self.assertNotIn("os.system", source)
        self.assertIsNone(re.search(r"\b[0-9a-fA-F]{40}\b", source))

    def test_cli_prints_the_report(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            plan_path = root / "plan.json"
            plan_path.write_text(json.dumps(PLAN), encoding="utf-8")
            out = root / "export"
            argv = [
                "--out",
                str(out),
                "--plan",
                str(plan_path),
                "--core-commit",
                SHA,
                "--author",
                "Ada Lovelace",
                "--source-url",
                "https://example.invalid/IEANTN",
                "--licence",
                "Apache-2.0",
                "--review-status",
                "unreviewed",
            ]
            with io.StringIO() as stdout, io.StringIO() as stderr:
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    code = project.main(argv)
                self.assertEqual(code, 0, stderr.getvalue())
                report = stdout.getvalue()
            self.assertIn("`Leaf.v1.main` is a hypothesis", report)
            self.assertTrue((out / "lakefile.toml").is_file())
            self.assertFalse((out / "lake-manifest.json").exists())


if __name__ == "__main__":
    unittest.main()
