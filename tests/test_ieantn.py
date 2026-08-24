"""Tests for the network tooling.

Run with:

    python -m unittest discover -s tests -v

Stdlib `unittest` deliberately, so a contributor needs no setup beyond what the tooling already
needs. The round-trip tests skip if `ruamel.yaml` is absent.

## What these are for

`scripts/ieantn.py` carries every invariant the network relies on, and until now was exercised only
by being run on a two-node repository where most branches never executed. Several tests below are
**regression tests for defects that actually shipped**, marked as such -- those are the valuable
ones, because each represents a failure a passing CI run did not catch.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import pathlib
import tempfile
import textwrap
import unittest

_SPEC = importlib.util.spec_from_file_location(
    "ieantn", pathlib.Path(__file__).resolve().parent.parent / "scripts" / "ieantn.py"
)
assert _SPEC and _SPEC.loader
ieantn = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(ieantn)


def node_yaml(node_id: str, conclusions: str, *, status: str = "active") -> str:
    """Build a node's metadata.

    The template below is written flush left on purpose. Interpolating into an *indented*
    triple-quoted string and calling `textwrap.dedent` afterwards does not work: dedent computes the
    common prefix across the interpolated text too, so the injected block silently sets the margin
    and the template's own lines come out misaligned. That produced fifteen unparseable fixtures the
    first time this file was written -- another instance of the silent-no-op class in the code audit.
    """
    family, version = node_id.rsplit(".", 1)
    body = textwrap.indent(textwrap.dedent(conclusions).strip("\n"), "  ")
    return f"""# A comment that must survive any round-trip through the tooling.
version: "v0.4"

node:
  id: {node_id}
  family: {family}
  version: {version}
  kind: paper
  status: {status}

project:
  name: "{node_id}"
  description: >-
    Fixture node.
  authors: ["Fixture"]
  license: "Apache-2.0"
  responsible_maintainers: ["Fixture"]

repository:
  role: substantive-development

classification:
  arxiv: [math.NT]
  msc2020: ["11N05"]

conclusions:
{body}

sources:
  - title: "Fixture source"
    authors: ["Fixture"]
    type: "paper"
    id: "https://example.invalid/fixture"
    relationship: formalizes
"""


LITERATURE = """
- id: main
  declaration: {node}.main
  challenge: {node}.challenge_main
  imports: []
  justifications:
    - id: paper
      kind: literature
  designated: paper
"""

IMPORTING = """
- id: main
  declaration: {node}.main
  challenge: {node}.challenge_main
  imports:
    - node: Upstream.v1
      conclusion: main
  justifications:
    - id: unjustified
      kind: none-yet
  designated: unjustified
"""


def bridged(source: str) -> str:
    return (
        "\n- id: main\n"
        "  declaration: {node}.main\n"
        "  challenge: {node}.challenge_main\n"
        "  imports: []\n"
        "  justifications:\n"
        "    - id: bridge\n"
        "      kind: bridged\n"
        f"      from: {source}\n"
        "      bridge: Bridges/a.lean\n"
        "  designated: bridge\n"
    )


def bridged_from(sources: list[str]) -> str:
    listed = "".join(f"        - {source}\n" for source in sources)
    return (
        "\n- id: main\n"
        "  declaration: {node}.main\n"
        "  challenge: {node}.challenge_main\n"
        "  imports: []\n"
        "  justifications:\n"
        "    - id: bridge\n"
        "      kind: bridged\n"
        "      from:\n"
        f"{listed}"
        "      bridge: Bridges/a.lean\n"
        "  designated: bridge\n"
    )


def importing(source_node: str) -> str:
    return (
        "\n- id: main\n"
        "  declaration: {node}.main\n"
        "  challenge: {node}.challenge_main\n"
        "  imports:\n"
        f"    - node: {source_node}\n"
        "      conclusion: main\n"
        "  justifications:\n"
        "    - id: u\n"
        "      kind: none-yet\n"
        "  designated: u\n"
    )


class FixtureRepo(unittest.TestCase):
    """A temporary repository that the real functions are pointed at."""

    def setUp(self) -> None:
        # The tooling prints progress for humans. Silence it so a failing assertion is the only
        # thing in the output.
        self._stack = contextlib.ExitStack()
        self._stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
        self.addCleanup(self._stack.close)
        self._original_root = ieantn.ROOT
        self._tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self._tmp.name)
        ieantn._set_root(self.root)
        (self.root / "IEANTN" / "Vocabulary").mkdir(parents=True)
        (self.root / "IEANTN" / "Nodes").mkdir(parents=True)
        (self.root / "lean-toolchain").write_text(
            "leanprover/lean4:v4.34.0-rc2\n", encoding="utf-8"
        )
        (self.root / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "mathlib", "rev": "a" * 40}]}), encoding="utf-8"
        )
        (self.root / "IEANTN" / "Nodes.lean").write_text("", encoding="utf-8")

    def tearDown(self) -> None:
        ieantn._set_root(self._original_root)
        self._tmp.cleanup()

    def write_node(self, node_id: str, conclusions: str, *, status: str = "active") -> pathlib.Path:
        family, version = node_id.rsplit(".", 1)
        directory = self.root / "IEANTN" / "Nodes" / family / version
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "formalization.yaml").write_text(
            node_yaml(node_id, conclusions.format(node=node_id), status=status), encoding="utf-8"
        )
        (directory / "Conclusions.lean").write_text(
            f"import IEANTN.Vocabulary\n\nnamespace {node_id}\n\ndef main : Prop := True\n\n"
            f"end {node_id}\n",
            encoding="utf-8",
        )
        return directory

    def write_bridge(self) -> None:
        (self.root / "Bridges").mkdir(exist_ok=True)
        (self.root / "Bridges" / "a.lean").write_text("-- bridge\n", encoding="utf-8")

    def generate(self) -> None:
        self.assertTrue(ieantn.gen_challenges(check_only=False))


class TestFixture(FixtureRepo):
    def test_the_fixture_itself_is_valid_yaml(self) -> None:
        """If this fails every other test in the file is meaningless."""
        self.write_node("Upstream.v1", LITERATURE)
        nodes = ieantn.load_nodes()
        self.assertIn("Upstream.v1", nodes)
        self.assertEqual(len(ieantn.conclusions_of(nodes["Upstream.v1"])), 1)


class TestGraphChecks(FixtureRepo):
    def test_wellformed_graph_passes(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("Downstream.v1", IMPORTING)
        self.generate()
        self.assertTrue(ieantn.check_graph())

    def test_import_of_unknown_node_fails(self) -> None:
        self.write_node("Downstream.v1", IMPORTING)
        self.assertFalse(ieantn.check_graph())

    def test_import_of_unexported_conclusion_fails(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("Downstream.v1", importing("Upstream.v1").replace("main\n", "absent\n", 1))
        self.assertFalse(ieantn.check_graph())

    def test_designated_naming_a_missing_justification_fails(self) -> None:
        self.write_node("Upstream.v1", LITERATURE.replace("designated: paper", "designated: nope"))
        self.assertFalse(ieantn.check_graph())

    def test_lean_comparator_without_receipt_fails(self) -> None:
        self.write_node(
            "Upstream.v1",
            LITERATURE.replace("kind: literature", "kind: lean-comparator"),
        )
        self.assertFalse(ieantn.check_graph())

    def test_lean_comparator_with_receipt_passes(self) -> None:
        self.write_node(
            "Upstream.v1", LITERATURE.replace("kind: literature", "kind: lean-comparator")
        )
        (self.root / "receipts").mkdir()
        (self.root / "receipts" / "Upstream.v1.main.json").write_text(
            json.dumps({"conclusion": "Upstream.v1.main"}), encoding="utf-8"
        )
        self.assertTrue(ieantn.check_graph())

    def _receipt_for(self, key: str) -> None:
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / f"{key}.json").write_text(
            json.dumps({"conclusion": key}), encoding="utf-8"
        )

    def test_a_receipt_nothing_designates_warns(self) -> None:
        """Regression: the first real verification landed exactly this way. The workflow wrote the
        receipt, the metadata still said `none-yet`, and `status` reported the node unverified --
        a verification had happened and the graph did not know."""
        self.write_node("A.v1", LITERATURE.replace("kind: literature", "kind: none-yet"))
        self._receipt_for("A.v1.main")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        self.assertTrue(passed, "an undesignated receipt is a warning, not an error")
        self.assertIn("has a receipt but designates", printed.getvalue())

    def test_a_designated_receipt_does_not_warn(self) -> None:
        self.write_node(
            "A.v1", LITERATURE.replace("kind: literature", "kind: lean-comparator")
        )
        self._receipt_for("A.v1.main")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertTrue(ieantn.check_graph())
        self.assertNotIn("has a receipt but designates", printed.getvalue())

    def test_template_status_is_refused(self) -> None:
        self.write_node("Upstream.v1", LITERATURE, status="template")
        self.assertFalse(ieantn.check_graph())

    def test_deprecated_without_superseded_by_fails(self) -> None:
        self.write_node("Upstream.v1", LITERATURE, status="deprecated")
        self.assertFalse(ieantn.check_graph())

    def test_declaration_name_mismatch_fails(self) -> None:
        self.write_node(
            "Upstream.v1", LITERATURE.replace("declaration: {node}.main", "declaration: Wrong.name")
        )
        self.assertFalse(ieantn.check_graph())

    def test_import_cycle_fails(self) -> None:
        self.write_node("A.v1", importing("B.v1"))
        self.write_node("B.v1", importing("A.v1"))
        self.assertFalse(ieantn.check_graph())

    def test_justification_transport_cycle_fails(self) -> None:
        """The soundness condition.

        Two versions each borrowing evidence from the other: both bridges check individually, the
        *import* graph stays acyclic, and nothing but this check stands between the network and a
        pair of conclusions justified by nothing at all.
        """
        self.write_bridge()
        self.write_node("A.v1", bridged("A.v2.main"))
        self.write_node("A.v2", bridged("A.v1.main"))
        self.assertFalse(ieantn.check_graph())

    def test_bridge_to_a_grounded_version_passes(self) -> None:
        self.write_bridge()
        self.write_node("A.v1", LITERATURE)
        self.write_node("A.v2", bridged("A.v1.main"))
        self.assertTrue(ieantn.check_graph())

    def test_missing_bridge_file_fails(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_node("A.v2", bridged("A.v1.main"))
        self.assertFalse(ieantn.check_graph())


class TestClosure(FixtureRepo):
    def test_vocabulary_may_not_leave_mathlib(self) -> None:
        (self.root / "IEANTN" / "Vocabulary" / "Bad.lean").write_text(
            "import PrimeNumberTheoremAnd.Defs\n", encoding="utf-8"
        )
        self.assertFalse(ieantn.check_closure())

    def test_conclusions_may_not_import_a_solution(self) -> None:
        directory = self.write_node("Upstream.v1", LITERATURE)
        (directory / "Conclusions.lean").write_text("import Solution\n", encoding="utf-8")
        self.assertFalse(ieantn.check_closure())

    def test_conclusions_may_import_mathlib_vocabulary_and_conclusions(self) -> None:
        directory = self.write_node("Upstream.v1", LITERATURE)
        (directory / "Conclusions.lean").write_text(
            "import Mathlib.Data.Nat.Basic\n"
            "import IEANTN.Vocabulary.PrimeGaps\n"
            "import IEANTN.Nodes.Other.v1.Conclusions\n",
            encoding="utf-8",
        )
        self.assertTrue(ieantn.check_closure())

    def _solution(self, toolchain: str | None) -> None:
        directory = self.root / "Solutions" / "A.v1"
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "lakefile.toml").write_text('name = "a"\n', encoding="utf-8")
        if toolchain is not None:
            (directory / "lean-toolchain").write_text(toolchain, encoding="utf-8")

    def test_a_solution_toolchain_matching_the_repository_passes(self) -> None:
        self._solution("leanprover/lean4:v4.34.0-rc2\n")
        self.assertTrue(ieantn.check_closure())

    def test_a_solution_pinning_a_different_toolchain_fails(self) -> None:
        """A path dependency is built with the root project's toolchain, so a divergent pin cannot
        work."""
        self._solution("leanprover/lean4:v4.30.0\n")
        self.assertFalse(ieantn.check_closure())

    def test_a_solution_with_no_toolchain_fails(self) -> None:
        """Regression: the first version of this rule *forbade* the file, reasoning that since a
        divergent pin cannot work there should be no pin. Mathlib's `cache` tool reads
        `lean-toolchain` from the project directory, so a solution without one compiles Mathlib
        from source rather than fetching it -- an hour instead of a minute. The rule is equality,
        not absence."""
        self._solution(None)
        self.assertFalse(ieantn.check_closure())


class TestChallengeGeneration(FixtureRepo):
    def test_generation_is_idempotent(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("Downstream.v1", IMPORTING)
        self.generate()
        self.assertTrue(ieantn.gen_challenges(check_only=True))

    def test_hand_edited_challenge_is_rejected(self) -> None:
        directory = self.write_node("Upstream.v1", LITERATURE)
        self.generate()
        challenge = directory / "Challenge.lean"
        challenge.write_text(
            challenge.read_text(encoding="utf-8") + "-- meddling\n", encoding="utf-8"
        )
        self.assertFalse(ieantn.gen_challenges(check_only=True))

    def test_imports_become_hypotheses(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("Downstream.v1", IMPORTING)
        self.generate()
        text = (self.root / "IEANTN/Nodes/Downstream/v1/Challenge.lean").read_text(encoding="utf-8")
        self.assertIn("upstream_v1_main : Upstream.v1.main", text)
        self.assertIn("sorry", text)

    def test_a_conclusion_with_no_imports_has_no_binders(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.generate()
        text = (self.root / "IEANTN/Nodes/Upstream/v1/Challenge.lean").read_text(encoding="utf-8")
        self.assertIn("theorem Upstream.v1.challenge_main : Upstream.v1.main := by", text)


class TestStaleness(FixtureRepo):
    def test_release_distance_compares_major_and_minor(self) -> None:
        """Regression: this ignored the major version, so v4.34 to v5.2 came out as 32 releases."""
        self.assertEqual(ieantn.release_distance("v4.33.0", "v4.34.0-rc2"), 1)
        self.assertEqual(ieantn.release_distance("v4.29.0", "v4.34.0-rc2"), 5)
        self.assertGreater(
            ieantn.release_distance("v4.34.0", "v5.2.0"), ieantn.CACHE_WINDOW_RELEASES
        )
        self.assertIsNone(ieantn.release_distance("not a toolchain", "v4.34.0"))

    def _receipt(self, statement: dict, environment: dict | None = None) -> dict:
        return {
            "schema": 1,
            "statement": statement,
            "environment": environment
            or {"lean_toolchain": "leanprover/lean4:v4.34.0-rc2", "mathlib_rev": "a" * 40},
        }

    def test_matching_statement_and_environment_is_green(self) -> None:
        light, _ = ieantn.assess(
            "A.v1.main", self._receipt({"A.v1.main": "d"}), {"A.v1.main": "d"}
        )
        self.assertEqual(light, "green")

    def test_own_statement_moved_is_broken(self) -> None:
        light, detail = ieantn.assess(
            "A.v1.main", self._receipt({"A.v1.main": "old"}), {"A.v1.main": "new"}
        )
        self.assertEqual(light, "BROKEN")
        self.assertIn("its own statement", detail)

    def test_imported_statement_moved_is_broken_and_names_it(self) -> None:
        """The graph-level property: an upstream edit breaks a downstream receipt."""
        light, detail = ieantn.assess(
            "B.v1.main",
            self._receipt({"B.v1.main": "d", "A.v1.main": "old"}),
            {"B.v1.main": "d", "A.v1.main": "new"},
        )
        self.assertEqual(light, "BROKEN")
        self.assertIn("A.v1.main", detail)

    def test_a_vanished_statement_is_broken(self) -> None:
        light, _ = ieantn.assess("A.v1.main", self._receipt({"A.v1.main": "d"}), {})
        self.assertEqual(light, "BROKEN")

    def test_environment_drift_is_yellow_not_broken(self) -> None:
        light, _ = ieantn.assess(
            "A.v1.main",
            self._receipt(
                {"A.v1.main": "d"},
                {"lean_toolchain": "leanprover/lean4:v4.33.0", "mathlib_rev": "b" * 40},
            ),
            {"A.v1.main": "d"},
        )
        self.assertEqual(light, "yellow")

    def test_far_behind_is_orange(self) -> None:
        light, _ = ieantn.assess(
            "A.v1.main",
            self._receipt(
                {"A.v1.main": "d"},
                {"lean_toolchain": "leanprover/lean4:v4.20.0", "mathlib_rev": "b" * 40},
            ),
            {"A.v1.main": "d"},
        )
        self.assertEqual(light, "orange")


class TestGraphQueries(FixtureRepo):
    def test_importers_are_found(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("Downstream.v1", IMPORTING)
        self.assertEqual(
            ieantn.importers_of(ieantn.load_nodes()),
            {"Upstream.v1.main": ["Downstream.v1.main"]},
        )

    def test_a_merely_older_version_is_not_a_deletion_task(self) -> None:
        """Versions are variants, not a succession: a newer version obsoletes nothing."""
        self.write_node("A.v1", LITERATURE)
        self.write_node("A.v2", LITERATURE)
        self.assertEqual(ieantn.importers_of(ieantn.load_nodes()), {})
        self.assertTrue(ieantn.housekeeping())

    def test_versions_of_orders_numerically(self) -> None:
        for version in ("v1", "v2", "v10"):
            self.write_node(f"A.{version}", LITERATURE)
        self.assertEqual([n for n, _ in ieantn.versions_of("A")], [1, 2, 10])


class TestScaffolding(FixtureRepo):
    def test_new_node_is_refused_until_filled_in(self) -> None:
        self.assertTrue(ieantn.new_node("Fresh", "paper"))
        self.assertFalse(ieantn.check_graph())

    def test_new_node_scaffold_is_internally_consistent(self) -> None:
        self.assertTrue(ieantn.new_node("Fresh", "paper"))
        self.assertTrue(ieantn.gen_challenges(check_only=True))

    def test_new_version_preserves_comments(self) -> None:
        """Regression: `yaml.safe_dump` silently discarded every comment, and the comments in these
        files carry the provenance."""
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.new_version("A"))
        text = (self.root / "IEANTN/Nodes/A/v2/formalization.yaml").read_text(encoding="utf-8")
        self.assertIn("# A comment that must survive", text)

    def test_new_version_does_not_repoint_imported_versions(self) -> None:
        """Regression: a blanket `v1` to `v2` rewrite silently repointed the new node's *imports*
        at a version of its dependency that did not exist."""
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("Downstream.v1", IMPORTING)
        self.assertTrue(ieantn.new_version("Downstream"))
        text = (self.root / "IEANTN/Nodes/Downstream/v2/formalization.yaml").read_text(
            encoding="utf-8"
        )
        self.assertIn("node: Upstream.v1", text)
        self.assertNotIn("Upstream.v2", text)

    def test_new_version_resets_the_justification(self) -> None:
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.new_version("A"))
        nodes = ieantn.load_nodes()
        self.assertEqual(
            ieantn.designated_kind(ieantn.conclusions_of(nodes["A.v2"])[0]), "none-yet"
        )

    def test_new_solution_does_not_import_the_challenge(self) -> None:
        """Comparator compares two modules declaring the same names, so importing the challenge
        would collide."""
        self.write_node("A.v1", LITERATURE)
        self.generate()
        self.assertTrue(ieantn.new_solution("A.v1"))
        text = (self.root / "Solutions/A.v1/Solution.lean").read_text(encoding="utf-8")
        self.assertIn("import IEANTN.Nodes.A.v1.Conclusions", text)
        self.assertNotIn("Challenge", text.split("/-!")[0])

    def test_new_solution_comparator_config_is_restricted(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.new_solution("A.v1"))
        config = json.loads(
            (self.root / "Solutions/A.v1/comparator.json").read_text(encoding="utf-8")
        )
        self.assertTrue(config["enable_nanoda"])
        self.assertEqual(
            sorted(config["permitted_axioms"]), ["Classical.choice", "Quot.sound", "propext"]
        )
        self.assertEqual(config["theorem_names"], ["A.v1.challenge_main"])

    def test_deprecate_requires_the_replacement_to_exist(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.assertFalse(ieantn.deprecate("A.v1", "A.v2"))


class TestNaryBridges(FixtureRepo):
    """A bridge may take several conclusions to one.

    That is the shape of splitting a node so separate groups can work on its parts in parallel and
    sewing it back together afterwards: `Part1.v1.main` and `Part2.v1.main` together imply
    `Whole.v1.main`. So a bridge is not only a relation between versions of one family.
    """

    def test_a_bridge_from_several_sources_passes(self) -> None:
        self.write_bridge()
        self.write_node("Part1.v1", LITERATURE)
        self.write_node("Part2.v1", LITERATURE)
        self.write_node("Whole.v1", bridged_from(["Part1.v1.main", "Part2.v1.main"]))
        self.assertTrue(ieantn.check_graph())

    def test_every_source_must_exist(self) -> None:
        self.write_bridge()
        self.write_node("Part1.v1", LITERATURE)
        self.write_node("Whole.v1", bridged_from(["Part1.v1.main", "Part2.v1.main"]))
        self.assertFalse(ieantn.check_graph())

    def test_a_cycle_through_one_source_of_many_is_caught(self) -> None:
        """The dangerous case: most sources are grounded, so the justification looks healthy, and
        one of them closes a loop back to the conclusion being justified."""
        self.write_bridge()
        self.write_node("Part1.v1", LITERATURE)
        self.write_node("Whole.v1", bridged_from(["Part1.v1.main", "Other.v1.main"]))
        self.write_node("Other.v1", bridged_from(["Whole.v1.main"]))
        self.assertFalse(ieantn.check_graph())

    def test_bridge_sources_accepts_one_or_many(self) -> None:
        self.assertEqual(ieantn.bridge_sources({"from": "A.v1.main"}), ["A.v1.main"])
        self.assertEqual(
            ieantn.bridge_sources({"from": ["A.v1.main", "B.v1.main"]}),
            ["A.v1.main", "B.v1.main"],
        )
        self.assertEqual(ieantn.bridge_sources({}), [])


class TestIssueLinking(FixtureRepo):
    def test_a_non_numeric_issue_fails(self) -> None:
        self.write_node(
            "A.v1",
            LITERATURE.replace("  designated: paper", "  issue: not-a-number\n  designated: paper"),
        )
        self.assertFalse(ieantn.check_graph())

    def test_a_numeric_issue_is_accepted(self) -> None:
        self.write_node(
            "A.v1", LITERATURE.replace("  designated: paper", "  issue: 42\n  designated: paper")
        )
        self.assertTrue(ieantn.check_graph())

    def test_unjustified_without_an_issue_warns_but_does_not_fail(self) -> None:
        """Work nobody can find is a problem for the project board, not for the graph."""
        self.write_node("A.v1", LITERATURE.replace("kind: literature", "kind: none-yet"))
        self.assertTrue(ieantn.check_graph())


class TestExamples(FixtureRepo):
    """A node may carry `Examples.lean`: consequences drawn from its own conclusions."""

    def _examples(self, node_id: str, text: str) -> None:
        family, version = node_id.rsplit(".", 1)
        (self.root / "IEANTN" / "Nodes" / family / version / "Examples.lean").write_text(
            text, encoding="utf-8"
        )

    def test_a_valid_examples_file_passes(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self._examples("A.v1", "import IEANTN.Nodes.A.v1.Conclusions\n\nexample : True := trivial\n")
        self.assertTrue(ieantn.check_closure())

    def test_examples_may_not_import_the_challenge(self) -> None:
        """The challenge is sorried, so an example resting on it proves anything, while looking
        exactly like one that proves something."""
        self.write_node("A.v1", LITERATURE)
        self._examples("A.v1", "import IEANTN.Nodes.A.v1.Challenge\n")
        self.assertFalse(ieantn.check_closure())

    def test_examples_may_not_contain_sorry(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self._examples("A.v1", "import IEANTN.Nodes.A.v1.Conclusions\n\nexample : True := by sorry\n")
        self.assertFalse(ieantn.check_closure())

    def test_the_word_sorry_in_a_comment_is_not_a_sorry(self) -> None:
        """Regression: the first version of this check matched the word in prose, and rejected the
        docstring that explains the rule."""
        self.write_node("A.v1", LITERATURE)
        self._examples(
            "A.v1",
            "import IEANTN.Nodes.A.v1.Conclusions\n\n"
            "/-! This file may not contain `sorry`. -/\n"
            "-- not even a sorry in a line comment\n"
            "example : True := trivial\n",
        )
        self.assertTrue(ieantn.check_closure())

    def test_examples_may_not_import_a_solution(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self._examples("A.v1", "import Solution\n")
        self.assertFalse(ieantn.check_closure())


class TestUmbrella(FixtureRepo):
    """`IEANTN/Nodes.lean` is generated, because while hand-maintained it drifted three times --
    each time silently, since a missing import only shows up as a module quietly not built."""

    def test_the_umbrella_is_generated_and_diffed(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.generate()
        self.assertTrue(ieantn.gen_challenges(check_only=True))
        umbrella = self.root / "IEANTN" / "Nodes.lean"
        umbrella.write_text(
            umbrella.read_text(encoding="utf-8") + "-- meddling\n", encoding="utf-8"
        )
        self.assertFalse(ieantn.gen_challenges(check_only=True))

    def test_every_node_appears(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", LITERATURE)
        self.generate()
        text = (self.root / "IEANTN" / "Nodes.lean").read_text(encoding="utf-8")
        self.assertIn("import IEANTN.Nodes.A.v1.Challenge", text)
        self.assertIn("import IEANTN.Nodes.B.v1.Challenge", text)

    def test_examples_are_imported_when_present_and_not_otherwise(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", LITERATURE)
        (self.root / "IEANTN" / "Nodes" / "A" / "v1" / "Examples.lean").write_text(
            "import IEANTN.Nodes.A.v1.Conclusions\n", encoding="utf-8"
        )
        self.generate()
        imports = (self.root / "IEANTN" / "Nodes.lean").read_text(encoding="utf-8").split("/-!")[0]
        self.assertIn("import IEANTN.Nodes.A.v1.Examples", imports)
        self.assertNotIn("B.v1.Examples", imports)

    def test_a_scaffolded_node_leaves_the_umbrella_current(self) -> None:
        """Regression: `new-node` wrote its own challenge but not the umbrella, so a fresh node
        was quietly not built."""
        self.assertTrue(ieantn.new_node("Fresh", "paper"))
        self.assertTrue(ieantn.gen_challenges(check_only=True))


class TestPins(FixtureRepo):
    """A Mathlib bump must not silently leave the verification toolchain behind."""

    def _script(self, toolchain: str | None) -> None:
        (self.root / "scripts").mkdir(exist_ok=True)
        declared = f"lean4export_toolchain={toolchain}\n" if toolchain else ""
        (self.root / "scripts" / "verify-comparator.sh").write_text(
            "#!/usr/bin/env bash\nlean4export_commit=abc\n" + declared, encoding="utf-8"
        )

    def test_a_matching_pin_passes(self) -> None:
        self._script("leanprover/lean4:v4.34.0-rc2")
        self.assertTrue(ieantn.check_pins())

    def test_a_stale_pin_fails(self) -> None:
        self._script("leanprover/lean4:v4.30.0")
        self.assertFalse(ieantn.check_pins())

    def test_an_undeclared_pin_fails(self) -> None:
        """Silence is not a pass: with nothing declared, nothing can be checked."""
        self._script(None)
        self.assertFalse(ieantn.check_pins())

    def test_no_script_is_not_a_failure(self) -> None:
        self.assertTrue(ieantn.check_pins())


class TestState(FixtureRepo):
    def test_state_is_generated_and_diffed(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.state(check_only=False))
        self.assertTrue(ieantn.state(check_only=True))
        (self.root / "STATE.md").write_text("stale\n", encoding="utf-8")
        self.assertFalse(ieantn.state(check_only=True))

    def test_state_counts_evidence_by_kind(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", LITERATURE.replace("kind: literature", "kind: none-yet"))
        ieantn.state(check_only=False)
        text = (self.root / "STATE.md").read_text(encoding="utf-8")
        self.assertIn("| `literature` | 1 |", text)
        self.assertIn("| `none-yet` | 1 |", text)

    def test_state_records_the_issue_and_the_leverage(self) -> None:
        self.write_node(
            "Upstream.v1",
            LITERATURE.replace("  designated: paper", "  issue: 42\n  designated: paper"),
        )
        self.write_node("Downstream.v1", IMPORTING)
        ieantn.state(check_only=False)
        text = (self.root / "STATE.md").read_text(encoding="utf-8")
        self.assertIn("#42", text)
        self.assertIn("| `Upstream.v1.main` | 1 |", text)


if __name__ == "__main__":
    unittest.main()
