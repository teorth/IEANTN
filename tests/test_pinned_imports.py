"""A verification may rest on a package outside Mathlib, provided it is pinned.

Settled in issue #164, along the line Palomar's specification draws for the same Comparator:
proof-only dependencies used by the Solution may be broader, but remain pinned and confined. The
confinement is the Challenge's Mathlib-only closure, which `check_closure` enforces elsewhere and
which holds by construction here, since a challenge lives in the Mathlib-only core. What is left
is the pin, and these are the three things that makes it worth something.
"""
import contextlib
import io
import json

from test_ieantn import FixtureRepo, LITERATURE, ieantn

PINNED = "6b11513512c9d27183fb4725bfc291ab38b4a6d7"


class TestPinnedImports(FixtureRepo):
    def write_solution(self, packages: list[dict], node_id: str = "A.v1") -> None:
        directory = self.root / "Solutions" / node_id
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "lakefile.toml").write_text('name = "s"\n', encoding="utf-8")
        (directory / "Solution.lean").write_text("-- proof\n", encoding="utf-8")
        (directory / "lean-toolchain").write_text(
            (self.root / "lean-toolchain").read_text(encoding="utf-8"), encoding="utf-8")
        (directory / "lake-manifest.json").write_text(
            json.dumps({"version": "1.1.0", "packages": packages}), encoding="utf-8")

    def core_manifest(self, packages: list[dict]) -> None:
        (self.root / "lake-manifest.json").write_text(
            json.dumps({"version": "1.1.0", "packages": packages}), encoding="utf-8")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n",
                                                  encoding="utf-8")

    def external(self, **overrides) -> dict:
        package = {"name": "leancert", "type": "git", "rev": PINNED,
                   "url": "https://github.com/alerad/leancert.git"}
        package.update(overrides)
        return package

    def setUp(self) -> None:
        super().setUp()
        self.write_node("A.v1", LITERATURE)
        self.core_manifest([{"name": "mathlib", "type": "git", "rev": "a" * 40,
                             "url": "https://github.com/leanprover-community/mathlib4"}])

    def test_a_full_commit_is_accepted(self) -> None:
        self.write_solution([self.external()])
        self.assertTrue(ieantn.check_closure())
        self.assertEqual(ieantn.solution_dependencies("A.v1"),
                         [{"name": "leancert", "url": "https://github.com/alerad/leancert.git",
                           "rev": PINNED}])

    def test_a_branch_is_not_a_pin(self) -> None:
        """It names whatever it names today, so a receipt pointing at one records a verification
        nobody can reproduce."""
        self.write_solution([self.external(rev="main")])
        self.assertFalse(ieantn.check_closure())

    def test_an_abbreviated_commit_is_not_a_pin(self) -> None:
        self.write_solution([self.external(rev=PINNED[:12])])
        self.assertFalse(ieantn.check_closure())

    def test_credentials_in_the_url_are_refused(self) -> None:
        """A pin anyone can fetch is part of what makes the verification repeatable."""
        self.write_solution([self.external(
            url="https://user:token@github.com/alerad/leancert.git")])
        self.assertFalse(ieantn.check_closure())

    def test_a_url_that_is_not_https_is_refused(self) -> None:
        self.write_solution([self.external(url="git://github.com/alerad/leancert.git")])
        self.assertFalse(ieantn.check_closure())

    def test_a_solution_may_not_pin_its_own_mathlib(self) -> None:
        """It would verify against a different library than the one the fingerprints were taken
        in, which is exactly what the receipt's environment is supposed to pin down."""
        self.write_solution([{"name": "mathlib", "type": "git", "rev": "b" * 40,
                              "url": "https://github.com/leanprover-community/mathlib4"}])
        self.assertFalse(ieantn.check_closure())

    def test_the_core_s_own_revision_is_fine(self) -> None:
        self.write_solution([{"name": "mathlib", "type": "git", "rev": "a" * 40,
                              "url": "https://github.com/leanprover-community/mathlib4"}])
        self.assertTrue(ieantn.check_closure())

    def test_a_solution_with_no_manifest_is_warned_about_not_refused(self) -> None:
        """The manifest is where the pin is written down. But a solution scaffolded by
        `new-solution` has none until someone resolves it, and nothing is unpinned at that point
        -- nothing is resolved. Refusing it would make `check` fail on a project's first day."""
        self.write_solution([self.external()])
        (self.root / "Solutions" / "A.v1" / "lake-manifest.json").unlink()
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertTrue(ieantn.check_closure())
        self.assertIn("lake-manifest.json", printed.getvalue())

    def test_the_path_dependency_on_the_core_is_not_an_external_import(self) -> None:
        self.write_solution([{"name": "IEANTN", "type": "path", "dir": "../.."},
                             self.external()])
        self.assertEqual([item["name"] for item in ieantn.solution_dependencies("A.v1")],
                         ["leancert"])

    def test_a_malformed_manifest_does_not_crash_the_reader(self) -> None:
        self.write_solution([self.external()])
        (self.root / "Solutions" / "A.v1" / "lake-manifest.json").write_text(
            "{not json", encoding="utf-8")
        self.assertEqual(ieantn.solution_dependencies("A.v1"), [])

    def test_the_node_page_says_what_the_proof_builds_on(self) -> None:
        """A reader deciding what a receipt is worth should not have to open a manifest."""
        self.write_solution([self.external()])
        nodes = ieantn.load_nodes()
        page = ieantn.render_node_page("A.v1", nodes, ieantn.index_conclusions(nodes),
                                       ieantn.importers_of(nodes))
        self.assertIn("Builds on", page)
        self.assertIn(f"/tree/{PINNED}", page)

    def test_a_node_that_adds_nothing_says_nothing(self) -> None:
        self.write_solution([{"name": "mathlib", "type": "git", "rev": "a" * 40,
                              "url": "https://github.com/leanprover-community/mathlib4"}])
        nodes = ieantn.load_nodes()
        page = ieantn.render_node_page("A.v1", nodes, ieantn.index_conclusions(nodes),
                                       ieantn.importers_of(nodes))
        self.assertNotIn("Builds on", page)
