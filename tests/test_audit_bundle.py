"""Stable audit manifests. A hash identifies bytes, not an unproved leaf."""

from __future__ import annotations

import importlib.util
import io
import json
import pathlib
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout


def load():
    path = pathlib.Path(__file__).resolve().parent.parent / "scripts" / "audit_bundle.py"
    spec = importlib.util.spec_from_file_location("audit_bundle", path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load()


def _populate(root: pathlib.Path) -> tuple[pathlib.Path, pathlib.Path]:
    (root / "Challenge.lean").write_text("theorem Spinoff.main : True := by\n  sorry\n", encoding="utf-8")
    (root / "lakefile.toml").write_text("name = \"ieantn_spinoff\"\n", encoding="utf-8")
    graph = root / "graph.json"
    graph.write_text(json.dumps({"nodes": ["A.v1"], "edges": []}, indent=2) + "\n", encoding="utf-8")
    metadata = root / "metadata.json"
    metadata.write_text(
        json.dumps({"core_commit": "d60421f10c16f5f6c2cb75f1067a72e24e616391", "author": "Ada"}, indent=2)
        + "\n",
        encoding="utf-8",
    )
    return graph, metadata


class AuditBundleTest(unittest.TestCase):
    def test_rerunning_writes_the_same_bytes_without_a_timestamp(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            graph, metadata = _populate(root)
            hypotheses = ["Leaf.v1.main", "Other.v1.main"]
            meta = json.loads(metadata.read_text(encoding="utf-8"))
            first = audit.write_manifest(root, graph, meta, hypotheses)
            second = audit.write_manifest(root, graph, meta, hypotheses)
            text = first.decode("utf-8")
            loaded = json.loads(text)
        self.assertEqual(first, second)
        self.assertNotIn('"timestamp"', text)
        self.assertNotIn('"generated_at"', text)
        self.assertNotIn('"mtime"', text)
        self.assertEqual(loaded["hypotheses"], hypotheses)
        self.assertEqual(loaded["metadata"]["author"], "Ada")
        self.assertEqual(loaded["graph"]["nodes"], ["A.v1"])
        self.assertEqual(loaded["reconstruction_note"], audit.RECONSTRUCTION_NOTE)
        self.assertIn("do not establish that an unproved hypothesis is true", loaded["reconstruction_note"])
        paths = [item["path"] for item in loaded["files"]]
        self.assertEqual(paths, ["Challenge.lean", "graph.json", "lakefile.toml", "metadata.json"])
        self.assertNotIn("audit/manifest.json", paths)

    def test_a_tampered_file_fails_the_check(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            graph, metadata = _populate(root)
            meta = json.loads(metadata.read_text(encoding="utf-8"))
            audit.write_manifest(root, graph, meta, ["Leaf.v1.main"])
            ok, message = audit.check_manifest(root)
            self.assertTrue(ok, message)
            self.assertIn("unproved hypothesis", message)
            challenge = root / "Challenge.lean"
            challenge.write_text(challenge.read_text(encoding="utf-8") + "-- tampered\n", encoding="utf-8")
            ok, message = audit.check_manifest(root)
        self.assertFalse(ok)
        self.assertIn("Challenge.lean", message)
        self.assertIn("sha256", message)
        self.assertNotIn("is true", message)

    def test_the_module_does_not_read_the_clock(self) -> None:
        source = pathlib.Path(audit.__file__).read_text(encoding="utf-8")
        self.assertNotIn("datetime", source)
        self.assertNotIn("time.time", source)

    def test_cli_check_rejects_the_tampered_project(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            graph, metadata = _populate(root)
            with io.StringIO() as stdout, io.StringIO() as stderr:
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    code = audit.main(
                        [
                            "write",
                            "--project",
                            str(root),
                            "--graph",
                            str(graph),
                            "--metadata",
                            str(metadata),
                            "--hypothesis",
                            "Leaf.v1.main",
                        ]
                    )
                self.assertEqual(code, 0, stderr.getvalue())
            (root / "lakefile.toml").write_bytes(b"name = \"changed\"\n")
            with io.StringIO() as stdout, io.StringIO() as stderr:
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    code = audit.main(["check", "--project", str(root)])
                self.assertEqual(code, 1)
                self.assertIn("lakefile.toml", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
