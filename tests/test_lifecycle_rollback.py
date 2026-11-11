"""A reported lifecycle failure must not leave a half-published graph."""
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
        (self.root / ".ieantn-edit.lock").write_text("another process")
        before = self.files()
        self.assertFalse(ieantn.new_version("A"))
        self.assertEqual(self.files(), before)

