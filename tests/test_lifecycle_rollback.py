"""A reported lifecycle failure must not leave a half-published graph."""
import os
import pathlib
import shutil
import subprocess
import sys
from unittest import mock

from test_ieantn import FixtureRepo, LITERATURE, ieantn


class LifecycleRollbackTests(FixtureRepo):
    def files(self):
        return {str(p.relative_to(self.root)): p.read_bytes()
                for p in self.root.rglob("*") if p.is_file()}

    def test_new_version_rolls_back_a_failed_generation(self):
        self.write_node("A.v1", LITERATURE)
        before = self.files()
        def failed(*args, **kwargs):
            (self.root / "IEANTN/Nodes.lean").write_text("partial umbrella")
            return False
        with mock.patch.object(ieantn, "gen_challenges", side_effect=failed):
            self.assertFalse(ieantn.new_version("A"))
        self.assertEqual(self.files(), before)

    def test_new_version_rolls_back_an_exception_during_generation(self):
        self.write_node("A.v1", LITERATURE)
        before = self.files()
        with mock.patch.object(ieantn, "gen_challenges", side_effect=OSError("disk failure")):
            with self.assertRaisesRegex(OSError, "disk failure"):
                ieantn.new_version("A")
        self.assertEqual(self.files(), before)

    def test_batch_deactivation_rolls_back_the_first_edit_when_second_fails(self):
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", LITERATURE)
        before = self.files()
        original = ieantn.edit_yaml
        def edit(path):
            if path.parent.parent.name == "B":
                raise OSError("second file unavailable")
            return original(path)
        with mock.patch.object(ieantn, "edit_yaml", side_effect=edit):
            with self.assertRaisesRegex(OSError, "second file"):
                ieantn.deactivate(["A.v1", "B.v1"], "test retirement")
        self.assertEqual(self.files(), before)

    def test_existing_edit_lock_refuses_to_touch_files(self):
        self.write_node("A.v1", LITERATURE)
        (self.root / ".ieantn-edit.lock").write_text("another process", encoding="utf-8")
        before = self.files()
        self.assertFalse(ieantn.new_version("A"))
        self.assertEqual(self.files(), before)

    def test_abandoned_edit_lock_is_not_staged_by_add_all(self):
        source_root = pathlib.Path(ieantn.__file__).resolve().parent.parent
        shutil.copyfile(source_root / ".gitignore", self.root / ".gitignore")
        (self.root / ".ieantn-edit.lock").write_text("abandoned lock", encoding="utf-8")
        git = ["git", "-c", f"core.excludesFile={os.devnull}", "-C", str(self.root)]
        subprocess.run(git + ["init", "--quiet", "--template="], check=True,
                       capture_output=True, text=True)
        subprocess.run(git + ["add", "--all"], check=True, capture_output=True, text=True)
        tracked = subprocess.run(git + ["ls-files"], check=True,
                                 capture_output=True, text=True).stdout.splitlines()
        self.assertIn(".gitignore", tracked)
        self.assertNotIn(".ieantn-edit.lock", tracked)

    def test_none_returning_edit_keeps_its_output(self):
        self.write_node("A.v1", LITERATURE)
        output = self.root / "IEANTN/Nodes/A/v1/retained.txt"

        @ieantn.checked_node_edit
        def edit():
            output.write_text("successful edit", encoding="utf-8")

        self.assertIsNone(edit())
        self.assertEqual(output.read_text(encoding="utf-8"), "successful edit")
        self.assertFalse((self.root / ".ieantn-edit.lock").exists())

    def test_successful_lifecycle_commands_release_the_lock(self):
        self.write_node("A.v1", LITERATURE)
        scripts = self.root / "scripts"
        scripts.mkdir()
        script = scripts / "ieantn.py"
        shutil.copyfile(ieantn.__file__, script)
        for arguments in (["new-version", "A"],
                          ["deactivate", "A.v2", "--reason", "fixture retirement"]):
            with self.subTest(arguments=arguments):
                result = subprocess.run([sys.executable, "-I", "-B", str(script), *arguments],
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertFalse((self.root / ".ieantn-edit.lock").exists())
        metadata = self.root / "IEANTN/Nodes/A/v2/formalization.yaml"
        self.assertEqual(ieantn.yaml.safe_load(metadata.read_text(encoding="utf-8"))
                         ["node"]["status"], "inactive")
