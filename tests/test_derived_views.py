# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: IEANTN contributors
#
"""Run the actual derived-view guard against synthetic pull-request histories."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import yaml


class TestDerivedViews(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        workflow = Path(__file__).resolve().parents[1] / ".github/workflows/ci.yml"
        cls.job = yaml.safe_load(workflow.read_text(encoding="utf-8"))["jobs"]["derived"]
        steps = [step for step in cls.job["steps"]
                 if step.get("name") == "No pull request writes the generated views"]
        if len(steps) != 1:
            raise AssertionError("expected exactly one derived-view guard step")
        cls.guard = steps[0]["run"]

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        # Fixtures must not inherit a caller's repository, hooks, merge drivers or shell startup.
        self.env = {key: value for key, value in os.environ.items()
                    if not key.startswith("GIT_") and key not in {"BASH_ENV", "ENV"}}
        self.env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        GIT_NO_LAZY_FETCH="1")
        self.git("init", "-q")
        self.views = ("STATE.md", "GRAPH.md", "docs/graph.html", "docs/nodes/synthetic.md")
        self.content = ("upstream=old\n" + "\n".join(f"stable-{i}" for i in range(20))
                        + "\nauthor=unchanged\n")
        self.initial_files = {path: self.content for path in self.views}
        self.initial_files.update({"docs/nodes/removable.md": "unchanged node\n",
                                   "source.py": "revision = 0\n"})
        self.initial = self.commit(self.initial_files, [], "initial event base")
        self.source_files = self.initial_files | {"source.py": "revision = 1\n"}
        self.head = self.commit(self.source_files, [self.initial], "source-only PR")
        self.upstream_files = self.initial_files | {
            path: self.content.replace("upstream=old", "upstream=new") for path in self.views}
        self.target = self.commit(self.upstream_files, [self.initial], "upstream views")

    def git(self, *args, data=None):
        result = subprocess.run(["git", *args], cwd=self.root, env=self.env, input=data,
                                capture_output=True, text=True, check=True, timeout=10)
        return result.stdout.strip()

    def tree(self, files):
        nested = {}
        for path, content in files.items():
            parent = nested
            parts = path.split("/")
            for part in parts[:-1]:
                parent = parent.setdefault(part, {})
            parent[parts[-1]] = self.git("hash-object", "-w", "--stdin", data=content)

        def make(entries):
            records = []
            for name, value in sorted(entries.items()):
                if isinstance(value, dict):
                    mode, kind, oid = "040000", "tree", make(value)
                else:
                    mode, kind, oid = "100644", "blob", value
                records.append(f"{mode} {kind} {oid}\t{name}\0")
            return self.git("mktree", "-z", data="".join(records))
        return make(nested)

    def commit_tree(self, tree, parents, label):
        # These are fixture objects, not contribution commits; no configured identity is changed.
        content = f"tree {tree}\n" + "".join(f"parent {parent}\n" for parent in parents)
        content += ("author Fixture <fixture@example.invalid> 0 +0000\n"
                    "committer Fixture <fixture@example.invalid> 0 +0000\n\n"
                    f"{label}\n")
        return self.git("hash-object", "-t", "commit", "-w", "--stdin", data=content)

    def commit(self, files, parents, label):
        return self.commit_tree(self.tree(files), parents, label)

    def merge(self, target, head):
        # Let Git actually merge the histories; a conflicting fixture must fail, not be hand-fixed.
        tree = self.git("merge-tree", "--write-tree", target, head)
        self.assertEqual(len(tree), 40)
        return self.commit_tree(tree, [target, head], "synthetic pull-request merge")

    def run_guard(self, checkout=None, event_base=None):
        if checkout is not None:
            self.git("update-ref", "HEAD", checkout)
        return subprocess.run(["bash", "-c", self.guard], cwd=self.root,
                              env=self.env | {"BASE": event_base or self.initial},
                              capture_output=True, text=True, timeout=10)

    def assert_passes(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("The generated views are untouched", result.stdout)

    def assert_rejects(self, result, path):
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("::error::This branch changes files", result.stdout)
        self.assertIn(path, result.stdout)

    def assert_fails_closed(self, result):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("The generated views are untouched", result.stdout)

    def test_checkout_retains_full_history_synthetic_merge(self):
        checkout = next(step for step in self.job["steps"]
                        if step.get("uses", "").startswith("actions/checkout@"))
        self.assertEqual(checkout["with"]["fetch-depth"], 0)
        self.assertNotIn("ref", checkout["with"])

    def test_stale_event_base_does_not_attribute_upstream_views_to_pr(self):
        self.assert_passes(self.run_guard(self.merge(self.target, self.head)))

    def test_aligned_event_base_still_accepts_source_only_pr(self):
        self.assert_passes(self.run_guard(self.merge(self.target, self.head), self.target))

    def test_upstream_views_merged_into_feature_are_not_authored_changes(self):
        integrated = self.merge(self.head, self.target)
        self.assert_passes(self.run_guard(self.merge(self.target, integrated)))

    def test_target_can_advance_again_after_feature_integrates_upstream(self):
        integrated = self.merge(self.head, self.target)
        files = self.upstream_files | {
            path: self.content.replace("upstream=old", "upstream=newer") for path in self.views}
        target = self.commit(files, [self.target], "target advances again")
        self.assert_passes(self.run_guard(self.merge(target, integrated), self.target))

    def test_each_guarded_view_rejects_an_authored_modification(self):
        for path in self.views:
            with self.subTest(path=path):
                files = self.source_files | {
                    path: self.content.replace("author=unchanged", "author=changed")}
                head = self.commit(files, [self.head], "authored view mutation")
                self.assert_rejects(self.run_guard(self.merge(self.target, head)), path)

    def test_authored_node_view_addition_is_rejected(self):
        path = "docs/nodes/added.md"
        head = self.commit(self.source_files | {path: "authored node view\n"},
                           [self.head], "authored view addition")
        self.assert_rejects(self.run_guard(self.merge(self.target, head)), path)

    def test_authored_node_view_deletion_is_rejected(self):
        path = "docs/nodes/removable.md"
        files = self.source_files.copy()
        del files[path]
        head = self.commit(files, [self.head], "authored view deletion")
        self.assert_rejects(self.run_guard(self.merge(self.target, head)), path)

    def test_authored_node_view_rename_is_rejected(self):
        files = self.source_files.copy()
        files["docs/nodes/renamed.md"] = files.pop("docs/nodes/removable.md")
        head = self.commit(files, [self.head], "authored view rename")
        self.assert_rejects(self.run_guard(self.merge(self.target, head)), "docs/nodes/renamed.md")

    def test_authored_view_after_upstream_integration_is_rejected(self):
        integrated = self.merge(self.head, self.target)
        files = self.upstream_files | {"source.py": "revision = 1\n"}
        files["GRAPH.md"] = files["GRAPH.md"].replace("author=unchanged", "author=changed")
        head = self.commit(files, [integrated], "authored edit after upstream integration")
        self.assert_rejects(self.run_guard(self.merge(self.target, head)), "GRAPH.md")

    def test_authored_view_identical_to_upstream_is_still_rejected(self):
        # Comparing only target -> merge would miss this genuine authored edit.
        head = self.commit(self.source_files | {"STATE.md": self.upstream_files["STATE.md"]},
                           [self.head], "authored view identical to upstream")
        combined = self.merge(self.target, head)
        self.assertEqual(self.git("diff", "--name-only", self.target, combined,
                                  "--", *self.views, "docs/nodes"), "")
        self.assert_rejects(self.run_guard(combined), "STATE.md")

    def test_single_parent_checkout_fails_closed(self):
        self.assert_fails_closed(self.run_guard(self.head))

    def test_root_checkout_fails_closed(self):
        self.assert_fails_closed(self.run_guard(self.initial))

    def test_unborn_checkout_fails_closed(self):
        self.assert_fails_closed(self.run_guard())

    def test_missing_merge_parent_fails_closed(self):
        malformed = self.commit_tree(self.tree(self.source_files),
                                     [self.initial, "f" * 40], "missing second parent")
        self.assert_fails_closed(self.run_guard(malformed))
