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
import unittest.mock

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
        "      bridge: IEANTN/Bridges/a.lean\n"
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
        "      bridge: IEANTN/Bridges/a.lean\n"
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

    def write_comparator_config(self, node_id: str, theorem_names: list[str] | None = None) -> None:
        """The solution config naming what Comparator was asked to check.

        `record-receipt` refuses without it: a receipt is written per conclusion, but Comparator
        runs once per node against exactly this list.
        """
        directory = self.root / "Solutions" / node_id
        directory.mkdir(parents=True, exist_ok=True)
        if theorem_names is None:
            node = ieantn.load_nodes()[node_id]
            theorem_names = [
                f"{node_id}.challenge_{c.get('id')}" for c in ieantn.conclusions_of(node)
            ]
        (directory / "comparator.json").write_text(
            json.dumps({"theorem_names": theorem_names}), encoding="utf-8"
        )

    def write_bridge(self, body: str = "-- bridge\n") -> pathlib.Path:
        directory = self.root / "IEANTN" / "Bridges"
        directory.mkdir(parents=True, exist_ok=True)
        written = directory / "a.lean"
        written.write_text(body, encoding="utf-8")
        return written

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

    def test_a_receipt_is_read_past_a_later_justification(self) -> None:
        """Regression: the warning must read the *designated* kind, not the last one listed.

        A conclusion may record further grounds after the one it designates -- a bridge from a
        sibling version, say. The check read the `kind` left over from the loop that validated the
        justifications, so recording any second ground made a properly verified node report as
        having a receipt nothing designates.
        """
        self.write_bridge()
        self.write_node("A.v1", LITERATURE)
        self.write_node(
            "A.v2",
            LITERATURE.replace("kind: literature", "kind: lean-comparator").replace(
                "  designated: paper\n",
                "    - id: bridge\n"
                "      kind: bridged\n"
                "      from: A.v1.main\n"
                "      bridge: IEANTN/Bridges/a.lean\n"
                "  designated: paper\n",
            ),
        )
        self._receipt_for("A.v2.main")
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

    def test_a_bridge_outside_the_library_fails(self) -> None:
        """A bridge nothing compiles attests nothing.

        The file merely existing at the recorded path is not evidence: it would go on satisfying
        this check after either statement it relates had moved out from under it. Requiring
        `IEANTN/Bridges/` puts it in the core build, where `lake build` notices.
        """
        (self.root / "Bridges").mkdir(exist_ok=True)
        (self.root / "Bridges" / "a.lean").write_text("-- bridge\n", encoding="utf-8")
        self.write_node("A.v1", LITERATURE)
        self.write_node(
            "A.v2", bridged("A.v1.main").replace("IEANTN/Bridges/a.lean", "Bridges/a.lean")
        )
        self.assertFalse(ieantn.check_graph())


class TestImportStatus(FixtureRepo):
    """Whether anyone has worked out what a claim assumes.

    An empty `imports` list means either "this rests on nothing" or "nobody has looked", and those
    are very different things to show a reader. The default is the second, so that the honest state
    is the one you get without doing anything.
    """

    def _with(self, status: str | None, imports: bool) -> None:
        body = importing("Upstream.v1") if imports else LITERATURE
        if status is not None:
            body = body.replace("  justifications:", f"  imports_status: {status}\n  justifications:")
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("A.v1", body)

    def test_absent_means_undetermined(self) -> None:
        self._with(None, imports=False)
        conclusion = ieantn.conclusions_of(ieantn.load_nodes()["A.v1"])[0]
        self.assertEqual(ieantn.import_status(conclusion), "undetermined")

    def test_an_unknown_status_is_refused(self) -> None:
        self._with("probably-fine", imports=False)
        self.assertFalse(ieantn.check_graph())

    def test_identified_with_no_imports_is_refused(self) -> None:
        """It is ambiguous exactly where precision matters, so the vocabulary has `none` for the
        case where someone looked and there was nothing."""
        self._with("identified", imports=False)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        self.assertFalse(passed)
        self.assertIn("say `none`", printed.getvalue())

    def test_none_with_imports_is_refused(self) -> None:
        self._with("none", imports=True)
        self.assertFalse(ieantn.check_graph())

    def test_identified_with_imports_passes(self) -> None:
        self._with("identified", imports=True)
        self.assertTrue(ieantn.check_graph())

    def test_none_without_imports_passes(self) -> None:
        self._with("none", imports=False)
        self.assertTrue(ieantn.check_graph())

    def test_undetermined_conclusions_are_queued(self) -> None:
        self._with(None, imports=False)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.housekeeping()
        self.assertIn("not yet traced to its sources", printed.getvalue())

    def test_traced_conclusions_are_not_queued(self) -> None:
        self._with("none", imports=False)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.housekeeping()
        self.assertNotIn("A.v1.main  (not yet traced", printed.getvalue())

    def test_the_graph_dashes_only_undetermined_boxes(self) -> None:
        self._with(None, imports=False)
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertIn("style A_v1_main stroke-dasharray: 2 3", rendered)
        self._with("none", imports=False)
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertNotIn("style A_v1_main stroke-dasharray", rendered)


class TestReceiptHealthInTheViews(FixtureRepo):
    """What the generated views say about a `lean-comparator` claim.

    They used to say `verified` for as long as the metadata designated it, which stayed true after
    an upstream edit had severed the very implication Comparator checked. `status` knew; the files
    a reader actually opens did not. These tests pin the three states apart.
    """

    def _verified(self, node_id: str, *, statement: dict | None = None,
                  mathlib_rev: str = "a" * 40, receipt: bool = True) -> str:
        """A node designating `lean-comparator`, with the receipt and fingerprints to match."""
        self.write_node(
            node_id, LITERATURE.replace("kind: literature", "kind: lean-comparator"))
        key = f"{node_id}.main"
        (self.root / "fingerprints.json").write_text(
            json.dumps({key: "digest-as-built"}), encoding="utf-8")
        if receipt:
            (self.root / "receipts").mkdir(exist_ok=True)
            (self.root / "receipts" / f"{key}.json").write_text(json.dumps({
                "conclusion": key,
                "statement": {key: "digest-as-built"} if statement is None else statement,
                "environment": {"lean_toolchain": "leanprover/lean4:v4.34.0-rc2",
                                "mathlib_rev": mathlib_rev},
            }), encoding="utf-8")
        return key

    def _kind_of(self, key: str) -> str:
        nodes = ieantn.load_nodes()
        return ieantn.display_kind(key, ieantn.index_conclusions(nodes)[key][1])

    def test_a_standing_receipt_is_plain_verified(self) -> None:
        self.assertEqual(self._kind_of(self._verified("A.v1")), "lean-comparator")

    def test_a_moved_statement_is_drifted(self) -> None:
        """The fingerprint the receipt pinned is not the one the library now elaborates to."""
        key = self._verified("A.v1", statement={"A.v1.main": "digest-before-the-edit"})
        self.assertEqual(self._kind_of(key), "lean-comparator-drifted")

    def test_a_moved_environment_is_only_stale(self) -> None:
        """Same two statements, different Mathlib: the proof still connects them."""
        key = self._verified("A.v1", mathlib_rev="b" * 40)
        self.assertEqual(self._kind_of(key), "lean-comparator-stale")

    def test_a_missing_receipt_is_drifted_not_verified(self) -> None:
        """Designating `lean-comparator` is a claim about a file; absent, it supports nothing."""
        self.assertEqual(
            self._kind_of(self._verified("A.v1", receipt=False)), "lean-comparator-drifted")

    def test_drift_outranks_environment_staleness(self) -> None:
        """A receipt can be both. Which one it is called is not a matter of taste: staleness is
        recoverable by re-running, and a severed implication is not."""
        key = self._verified(
            "A.v1", statement={"A.v1.main": "digest-before-the-edit"}, mathlib_rev="b" * 40)
        self.assertEqual(self._kind_of(key), "lean-comparator-drifted")

    def test_a_drifted_receipt_ranks_below_a_bare_assertion(self) -> None:
        """An assertion is a claim someone stands behind. A voided receipt supports nothing about
        the statement as it now reads, so it must not summarise a node more favourably."""
        order = ieantn.EVIDENCE_ORDER
        self.assertLess(order.index("lean-comparator-drifted"), order.index("asserted"))
        self.assertLess(order.index("lean-comparator-stale"), order.index("lean-comparator"))
        self.assertLess(order.index("bridged"), order.index("lean-comparator-stale"))

    def test_the_overview_box_says_drifted(self) -> None:
        """The point of the exercise: it has to be legible without running the tooling."""
        self._verified("A.v1", statement={"A.v1.main": "digest-before-the-edit"})
        nodes = ieantn.load_nodes()
        rendered = chr(10).join(
            ieantn.render_node_overview(nodes, ieantn.index_conclusions(nodes)))
        self.assertIn("verified, drifted", rendered)
        self.assertIn("lean_comparator_drifted", rendered)

    def test_state_names_the_claim_that_moved(self) -> None:
        """A pull request that voids a receipt should carry that fact in its own diff."""
        self._verified("A.v1", statement={"A.v1.main": "digest-before-the-edit"})
        rendered = ieantn.render_state(ieantn.load_nodes())
        self.assertIn("Receipts needing attention", rendered)
        self.assertIn("A.v1.main", rendered)

    def test_state_is_silent_when_every_receipt_stands(self) -> None:
        self._verified("A.v1")
        self.assertNotIn(
            "Receipts needing attention", ieantn.render_state(ieantn.load_nodes()))


class TestNodeOverview(FixtureRepo):
    """The collapsed, one-box-per-node picture.

    The per-conclusion graph is the true one, but it grows with the number of claims and stops
    being legible long before the network stops being useful. This one grows with the number of
    papers instead, which is the scale a reader can hold in their head.
    """

    def _overview(self) -> str:
        nodes = ieantn.load_nodes()
        return chr(10).join(ieantn.render_node_overview(nodes, ieantn.index_conclusions(nodes)))

    def test_a_node_is_summarised_by_its_weakest_claim(self) -> None:
        """Nine computed claims and one citation is, to anyone importing the node, a citation."""
        self.assertEqual(
            ieantn.weakest_kind("A.v1",
                                [{"id": f"c{index}",
                                  "justifications": [{"id": "j", "kind": kind}],
                                  "designated": "j"}
                                 for index, kind in enumerate(("numerical", "literature"))]),
            "literature")

    def test_an_edge_is_drawn_between_the_nodes_not_the_claims(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("A.v1", importing("Upstream.v1"))
        self.assertIn("NUpstream_v1 --> NA_v1", self._overview())

    def test_a_node_with_nothing_stated_still_appears(self) -> None:
        """A recorded paper with no claim yet is an open invitation, not an absence."""
        self.write_node("Upstream.v1", LITERATURE)
        rendered = self._overview()
        self.assertIn("NUpstream_v1", rendered)

    def test_the_overview_dashes_a_node_with_any_untraced_claim(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.assertIn("style NUpstream_v1 stroke-dasharray", self._overview())

    def test_both_pictures_are_in_the_page(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertIn("## The network at a glance", rendered)
        self.assertIn("## Every claim", rendered)
        self.assertIn('subgraph sgUpstream_v1["Upstream.v1"]', rendered)


class TestBridgesInTheGraph(FixtureRepo):
    """A bridge is drawn as a node, not an arrow.

    Two reasons, and the second is the one that forces it. First, an import arrow and a bridge are
    different relations -- one says "assumes, unchecked", the other says "proved in Lean, and
    recompiled on every push" -- and drawing them alike would make the picture claim more or less
    verification than there is. Second, `from` may name several conclusions, so a bridge is an
    implication with several hypotheses; an arrow cannot say which premises were needed together,
    and a node with several arrows into it can.
    """

    def _bridged(self, premises: list[str]) -> dict:
        self.write_node("Up.v1", LITERATURE)
        self.write_node("Up2.v1", LITERATURE)
        body = LITERATURE.replace(
            "  designated:",
            "    - id: br" + chr(10)
            + "      kind: bridged" + chr(10)
            + "      from: [" + ", ".join(premises) + "]" + chr(10)
            + "      bridge: IEANTN/Bridges/Fam/Sewn.lean" + chr(10)
            + "  designated:")
        self.write_node("A.v1", body)
        return ieantn.load_nodes()

    def test_a_many_premise_bridge_is_one_node_with_two_arrows_in(self) -> None:
        nodes = self._bridged(["Up.v1.main", "Up2.v1.main"])
        found = ieantn.bridges_in(nodes)
        self.assertEqual(len(found), 1)
        self.assertEqual(sorted(found[0]["premises"]), ["Up.v1.main", "Up2.v1.main"])
        rendered = ieantn.render_graph(nodes)
        self.assertIn("Up_v1_main ==> BR", rendered)
        self.assertIn("Up2_v1_main ==> BR", rendered)

    def test_the_bridge_node_is_a_hexagon_named_for_its_file(self) -> None:
        rendered = ieantn.render_graph(self._bridged(["Up.v1.main"]))
        self.assertIn('{{"<b>Sewn</b>', rendered)

    def test_a_bridge_that_is_not_designated_says_so(self) -> None:
        """A spare ground is still real evidence and still worth drawing, but a reader should not
        mistake it for the one the claim currently rests on."""
        rendered = ieantn.render_graph(self._bridged(["Up.v1.main"]))
        self.assertIn("<i>spare</i>", rendered)

    def test_the_overview_shows_a_bridge_between_the_nodes(self) -> None:
        nodes = self._bridged(["Up.v1.main"])
        rendered = chr(10).join(
            ieantn.render_node_overview(nodes, ieantn.index_conclusions(nodes)))
        self.assertIn("NUp_v1 ==>|bridge| NA_v1", rendered)

    def test_mermaid_ids_survive_dots_dashes_and_colons(self) -> None:
        """Every one of these appears in a real key, and each ends a Mermaid id early."""
        self.assertEqual(ieantn.mermaid_id("Lcm.v1.main::br-2"), "Lcm_v1_main__br_2")


class TestDeclarationLinks(FixtureRepo):
    """Every claim in the graph links to the line of Lean that states it.

    Without this a reader has the node id and nothing else: they must guess the path from the id
    and then search the file. The link is to source rather than to generated documentation because
    source needs no hosting and no second build; `declaration_url` is the single place to change
    when doc-gen is published.
    """

    def _lean(self, body: str) -> None:
        path = self.root / "IEANTN" / "Nodes" / "A" / "v1" / "Conclusions.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")

    def test_it_finds_the_defining_line(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self._lean("import X" + chr(10) + chr(10) + "def other : Prop := True"
                   + chr(10) + "def main : Prop := True" + chr(10))
        self.assertTrue(ieantn.declaration_url("A.v1.main").endswith("Conclusions.lean#L4"))

    def test_a_noncomputable_definition_is_found_too(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self._lean("noncomputable def main : Prop := True" + chr(10))
        self.assertTrue(ieantn.declaration_url("A.v1.main").endswith("#L1"))

    def test_a_name_that_merely_starts_the_same_is_not_matched(self) -> None:
        """`main_lemma` must not answer for `main`, or the link lands on the wrong claim."""
        self.write_node("A.v1", LITERATURE)
        self._lean("def main_lemma : Prop := True" + chr(10) + "def main : Prop := True" + chr(10))
        self.assertTrue(ieantn.declaration_url("A.v1.main").endswith("#L2"))

    def test_a_missing_declaration_gives_no_link_rather_than_a_wrong_one(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self._lean("def something_else : Prop := True" + chr(10))
        self.assertIsNone(ieantn.declaration_url("A.v1.main"))

    def test_the_page_makes_the_boxes_clickable(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self._lean("def main : Prop := True" + chr(10))
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertIn("click A_v1_main href", rendered)
        self.assertIn("[`A.v1.main`](", rendered)


class TestNodePages(FixtureRepo):
    """One page per node, for a reader who is not going to open the YAML.

    A node's claim is only as good as what stands behind it, and that lives in
    `formalization.yaml` in a shape built for machines. The page is the same content for a person,
    with the Lean spelling next to each claim -- which is what a consumer has to write, and what
    decides whether a transcription is faithful.
    """

    def _node(self, lean: str = "") -> None:
        self.write_node("A.v1", LITERATURE)
        path = self.root / "IEANTN" / "Nodes" / "A" / "v1" / "Conclusions.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(lean, encoding="utf-8")

    def _page(self) -> str:
        ieantn.pages(False)
        return (self.root / "docs" / "nodes" / "A-v1.md").read_text(encoding="utf-8")

    def test_the_lean_spelling_is_on_the_page(self) -> None:
        self._node("/-- The claim. -/" + chr(10)
                   + "def main : Prop :=" + chr(10) + "  True" + chr(10))
        page = self._page()
        self.assertIn("def main : Prop :=", page)
        self.assertIn("  True", page)

    def test_the_docstring_is_on_the_page(self) -> None:
        """It is where the informal statement lives -- there is no blueprint."""
        self._node("/-- The **informal** statement. -/" + chr(10) + "def main : Prop := True" + chr(10))
        self.assertIn("The **informal** statement.", self._page())

    def test_the_body_stops_at_the_next_declaration(self) -> None:
        self._node("def main : Prop := True" + chr(10) + chr(10)
                   + "def later : Prop := False" + chr(10))
        page = self._page()
        self.assertIn("def main", page)
        self.assertNotIn("def later", page)

    def test_pages_link_to_each_other_relatively(self) -> None:
        """They sit together in docs/nodes/, so a rooted path would be broken between them."""
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("A.v1", importing("Upstream.v1"))
        ieantn.pages(False)
        page = (self.root / "docs" / "nodes" / "A-v1.md").read_text(encoding="utf-8")
        self.assertIn("](Upstream-v1.md#main)", page)

    def test_the_graph_links_to_pages_from_the_repository_root(self) -> None:
        """And GRAPH.md sits at the root, so the same link needs the prefix."""
        self._node("def main : Prop := True" + chr(10))
        self.assertIn("](docs/nodes/A-v1.md#main)", ieantn.render_graph(ieantn.load_nodes()))

    def test_mermaid_clicks_are_absolute(self) -> None:
        """GitHub renders Mermaid in a sandbox on viewscreen.githubusercontent.com, so a relative
        click href resolves against that origin and 404s. Markdown links on the same page are
        fine. Nothing local or in CI can catch this, so it is pinned here."""
        self._node("def main : Prop := True" + chr(10))
        rendered = ieantn.render_graph(ieantn.load_nodes())
        for line in rendered.splitlines():
            if line.strip().startswith("click "):
                self.assertIn('href "https://github.com/', line)

    def test_a_page_for_a_node_that_no_longer_exists_is_removed(self) -> None:
        self._node("def main : Prop := True" + chr(10))
        ieantn.pages(False)
        stale = self.root / "docs" / "nodes" / "Gone-v1.md"
        stale.write_text("leftover", encoding="utf-8")
        ieantn.pages(False)
        self.assertFalse(stale.exists())

    def test_check_fails_when_a_page_is_stale(self) -> None:
        self._node("def main : Prop := True" + chr(10))
        ieantn.pages(False)
        (self.root / "docs" / "nodes" / "A-v1.md").write_text("stale", encoding="utf-8")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.pages(True)
        self.assertFalse(passed)
        self.assertIn("out of date", printed.getvalue())

    def test_the_page_links_the_solution_and_receipt_when_they_exist(self) -> None:
        """Naming a path without linking it made readers rebuild the URL by hand, which is the
        friction that stops people checking evidence at all."""
        self._node("def main : Prop := True" + chr(10))
        (self.root / "Solutions" / "A.v1").mkdir(parents=True, exist_ok=True)
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / "A.v1.main.json").write_text("{}", encoding="utf-8")
        page = self._page()
        self.assertIn("/tree/main/Solutions/A.v1)", page)
        self.assertIn("/blob/main/receipts/A.v1.main.json)", page)

    def test_no_solution_row_when_there_is_no_solution(self) -> None:
        self._node("def main : Prop := True" + chr(10))
        self.assertNotIn("| Solution |", self._page())

    def test_a_node_stating_nothing_still_gets_a_page(self) -> None:
        self.write_node("Empty.v1", "[]" + chr(10))
        ieantn.pages(False)
        page = (self.root / "docs" / "nodes" / "Empty-v1.md").read_text(encoding="utf-8")
        self.assertIn("states nothing yet", page)


class TestVerifyApprovalNotice(FixtureRepo):
    """A verification parked at the approval gate must say so.

    `gh run watch` draws a run that has not started identically to one that is building, and the
    difference is plainly visible in the API. Someone once waited thirty-two minutes for a run that
    had executed nothing at all.
    """

    def _run(self, states: list[str]) -> str:
        """Drive `verify` through a scripted sequence of run states."""
        remaining = list(states)

        def fake(args: list[str]) -> str:
            if args[0] == "run":
                return "424242"
            if args[-1].endswith("@tsv"):
                state = remaining.pop(0)
                return state + ("\tsuccess" if state == "completed" else "\t")
            return ""

        printed = io.StringIO()
        with unittest.mock.patch.object(ieantn, "_gh_json", fake), \
             unittest.mock.patch.object(ieantn.time, "sleep", lambda _: None), \
             unittest.mock.patch.object(ieantn, "repository_slug", lambda: "teorth/IEANTN"), \
             contextlib.redirect_stdout(printed):
            ieantn.verify("A.v1", "some-branch", dispatch=False)
        return printed.getvalue()

    def test_a_waiting_run_asks_for_approval_and_gives_the_url(self) -> None:
        out = self._run(["waiting", "completed"])
        self.assertIn("WAITING FOR YOUR APPROVAL", out)
        self.assertIn("https://github.com/teorth/IEANTN/actions/runs/424242", out)

    def test_it_says_what_approving_means(self) -> None:
        """The gate exists because a human is supposed to have looked at the branch."""
        self.assertIn("vouching for this branch's core Lean", self._run(["waiting", "completed"]))

    def test_the_notice_is_printed_once_not_every_poll(self) -> None:
        out = self._run(["waiting", "waiting", "waiting", "completed"])
        self.assertEqual(out.count("WAITING FOR YOUR APPROVAL"), 1)

    def test_a_run_that_never_waits_says_nothing_about_approval(self) -> None:
        self.assertNotIn("WAITING", self._run(["in_progress", "completed"]))

    def test_the_conclusion_is_reported(self) -> None:
        out = self._run(["completed"])
        self.assertIn("completed: success", out)


class TestTracedStatus(FixtureRepo):
    """`traced`: the inputs are known, and at least one of them is not an edge.

    `undetermined` was doing two jobs. "Nobody has looked at this verification" and "it rests on
    Trudgian's Theorem 4.2, Whittaker-Shannon sampling, a subconvexity bound, and its own FFT, of
    which only the third could currently be an edge" are not the same state, and rendering them
    identically threw away the second one's work.
    """

    def _with(self, status: str, imports: bool = True) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        body = importing("Upstream.v1") if imports else LITERATURE
        body = body.replace("  justifications:", f"  imports_status: {status}\n  justifications:")
        self.write_node("A.v1", body)

    def test_traced_is_accepted_with_imports(self) -> None:
        self._with("traced")
        self.assertTrue(ieantn.check_graph())

    def test_traced_is_accepted_without_imports(self) -> None:
        """Every input may be undrawable -- a pure computation resting on an algorithm."""
        self._with("traced", imports=False)
        self.assertTrue(ieantn.check_graph())

    def test_traced_needs_somewhere_for_the_tracing_to_live(self) -> None:
        """The note is the only place the named inputs can be, so a justification is required."""
        self.write_node("A.v1", LITERATURE.replace(
            "  justifications:\n    - id: paper\n      kind: literature\n  designated: paper",
            "  imports_status: traced\n  justifications: []\n  designated: paper"))
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        self.assertFalse(passed)
        self.assertIn("nowhere for the tracing to live", printed.getvalue())

    def test_the_graph_dots_traced_and_dashes_undetermined(self) -> None:
        """Three states, three renderings; collapsing any two loses the distinction."""
        self._with("traced")
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertIn("style A_v1_main stroke-dasharray: 8 4", rendered)
        self.assertNotIn("style A_v1_main stroke-dasharray: 2 3", rendered)

    def test_traced_is_not_queued_by_housekeeping(self) -> None:
        """Some missing edges await a node that could exist and some await one that never can;
        nothing can tell those apart, and an unactionable queue is worse than none."""
        self._with("traced")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.housekeeping()
        self.assertNotIn("A.v1.main  (not yet traced", printed.getvalue())

    def test_undetermined_is_still_queued(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.housekeeping()
        self.assertIn("not yet traced to its sources", printed.getvalue())


class TestProgressMarker(FixtureRepo):
    """A partial solution is tracked, and is never mistaken for evidence.

    `justification` records what a claim rests on; `progress` records what someone is doing. A
    partial proof with seven holes supports nothing, and conflating the two would corrupt the one
    report this repository exists to produce.
    """

    def _with_progress(self, marker: str) -> None:
        self.write_node("A.v1", LITERATURE.replace(
            "  designated: paper", "  designated: paper" + chr(10) + marker))

    def test_a_well_formed_marker_passes(self) -> None:
        self._with_progress("  progress:" + chr(10)
                            + "    solution: Solutions/A.v1/" + chr(10)
                            + "    state: in-progress" + chr(10)
                            + "    remaining_holes: 7")
        self.assertTrue(ieantn.check_graph())

    def test_an_unknown_state_is_refused(self) -> None:
        self._with_progress("  progress:" + chr(10) + "    state: nearly-there")
        self.assertFalse(ieantn.check_graph())

    def test_a_hand_written_hole_count_must_be_a_number(self) -> None:
        """It is derived by `progress --write`; a string here means someone typed a guess."""
        self._with_progress("  progress:" + chr(10)
                            + "    state: in-progress" + chr(10)
                            + '    remaining_holes: "about seven"')
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        self.assertFalse(passed)
        self.assertIn("derive it", printed.getvalue())

    def test_a_marker_left_on_a_verified_conclusion_is_refused(self) -> None:
        """`record-receipt` clears it; one left behind says work is outstanding on something
        already done."""
        self.write_node("A.v1", LITERATURE.replace(
            "      kind: literature", "      kind: lean-comparator").replace(
            "  designated: paper",
            "  designated: paper" + chr(10) + "  progress:" + chr(10) + "    state: in-progress"))
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / "A.v1.main.json").write_text(
            json.dumps({"conclusion": "A.v1.main"}), encoding="utf-8")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        self.assertFalse(passed)
        self.assertIn("already done", printed.getvalue())

    def test_a_missing_solution_is_reported_not_crashed(self) -> None:
        self.write_node("A.v1", LITERATURE)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.progress("A.v1", write=False)
        self.assertFalse(passed)
        self.assertIn("no solution", printed.getvalue())


class TestGraphPage(FixtureRepo):
    """`GRAPH.md`: the network as a page someone can read without cloning anything.

    The dependency structure is the repository's headline output, and until this existed it could
    only be seen by running `report` locally. Generated and committed, like the other derived
    files, so the picture and the prose cannot drift apart or from the metadata.
    """

    def _chain(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node(
            "A.v1", importing("Upstream.v1").replace("kind: none-yet", "kind: lean-comparator"))
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / "A.v1.main.json").write_text(
            json.dumps({"conclusion": "A.v1.main"}), encoding="utf-8")

    def test_it_draws_an_edge_for_each_import(self) -> None:
        self._chain()
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertIn("Upstream_v1_main --> A_v1_main", rendered)

    def test_mermaid_ids_carry_no_dots(self) -> None:
        """Mermaid rejects dots in node ids, and a conclusion key is full of them."""
        self.assertEqual(ieantn.mermaid_id("A.v1.main-x"), "A_v1_main_x")

    def test_only_roots_head_the_trees(self) -> None:
        """An imported conclusion appears inside the tree of whatever imports it, not as its own
        heading -- otherwise every leaf is listed twice and the shape is lost."""
        self._chain()
        rendered = ieantn.render_graph(ieantn.load_nodes())
        trees = rendered.split("## What each result rests on")[1].split("##")[0]
        self.assertIn("- [`A.v1.main`](", trees)
        self.assertNotIn("@- [`Upstream.v1.main`](", trees.replace("@", ""))
        self.assertIn("  - [`Upstream.v1.main`](", trees)

    def test_the_trust_table_ranks_by_dependants(self) -> None:
        """The honest answer to "how good is the evidence" is which unproved claims carry the most
        weight, and it is computed rather than maintained."""
        self._chain()
        rendered = ieantn.render_graph(ieantn.load_nodes())
        table = rendered.split("## What the network takes on trust")[1]
        self.assertIn("`Upstream.v1.main`", table)
        self.assertNotIn("`A.v1.main`", table.split("##")[0])

    def test_a_cycle_free_repeat_is_marked_not_expanded(self) -> None:
        """A diamond would otherwise be printed twice at full depth, and a cycle would not
        terminate at all."""
        self.write_node("Base.v1", LITERATURE)
        for node in ("Left.v1", "Right.v1"):
            self.write_node(node, importing("Base.v1"))
        top = ("@- id: main@  declaration: {node}.main@  challenge: {node}.challenge_main@"
               "  imports:@    - node: Left.v1@      conclusion: main@"
               "    - node: Right.v1@      conclusion: main@  justifications:@    - id: u@"
               "      kind: none-yet@  designated: u@").replace("@", chr(10))
        self.write_node("Top.v1", top)
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertIn("*(above)*", rendered)

    def test_conclusionless_nodes_get_their_own_section(self) -> None:
        self.write_node("Paper.v1", "[]", status="stub")
        rendered = ieantn.render_graph(ieantn.load_nodes())
        self.assertIn("Nodes that state nothing yet", rendered)
        self.assertIn("`Paper.v1`", rendered)

    def test_check_mode_notices_staleness(self) -> None:
        self._chain()
        (self.root / "GRAPH.md").write_text("stale\n", encoding="utf-8")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertFalse(ieantn.graph(check_only=True))
        self.assertTrue(ieantn.graph(check_only=False))
        self.assertTrue(ieantn.graph(check_only=True))


class TestConclusionlessNodes(FixtureRepo):
    """A node may state nothing yet, and must still be visible.

    Starting a paper as a stub and adding conclusions later is a supported workflow. It only works
    if the tooling can see the stub: every report iterates conclusions, so before this a node with
    none appeared in `report`, `status`, `housekeeping` and `STATE.md` exactly nowhere -- and the
    graph is meant to *be* the task queue, so a task it cannot show is not queued.
    """

    def _stub(self, node_id: str = "Paper.v1", *, status: str = "stub") -> pathlib.Path:
        directory = self.root / "IEANTN" / "Nodes" / node_id.replace(".", "/")
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "formalization.yaml").write_text(
            node_yaml(node_id, "[]", status=status), encoding="utf-8")
        (directory / "Conclusions.lean").write_text(
            "import IEANTN.Vocabulary\n", encoding="utf-8")
        return directory

    def test_a_node_with_no_conclusions_passes_the_checks(self) -> None:
        self._stub()
        self.assertTrue(ieantn.check_graph())
        self.assertTrue(ieantn.check_closure())

    def test_its_generated_challenge_has_no_theorems(self) -> None:
        self._stub()
        self.generate()
        challenge = (self.root / "IEANTN" / "Nodes" / "Paper" / "v1" / "Challenge.lean")
        self.assertTrue(challenge.is_file())
        self.assertNotIn("theorem", challenge.read_text(encoding="utf-8"))

    def test_it_appears_in_the_housekeeping_queue(self) -> None:
        self._stub()
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.housekeeping()
        self.assertIn("Paper.v1", printed.getvalue())
        self.assertIn("no conclusions yet", printed.getvalue())

    def test_it_gets_a_row_in_the_state_snapshot(self) -> None:
        self._stub()
        rendered = ieantn.render_state(ieantn.load_nodes())
        self.assertIn("`Paper.v1`", rendered)
        self.assertIn("state nothing yet", rendered)

    def test_a_deprecated_stub_is_not_queued(self) -> None:
        """Deprecation already says "this should go away"; asking for conclusions would be noise."""
        directory = self._stub(status="deprecated")
        text = (directory / "formalization.yaml").read_text(encoding="utf-8")
        (directory / "formalization.yaml").write_text(
            text.replace("  status: deprecated", "  status: deprecated\n  superseded_by: Paper.v1"),
            encoding="utf-8")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.housekeeping()
        self.assertNotIn("no conclusions yet", printed.getvalue())


class TestSolutionDrift(FixtureRepo):
    """A receipt attests to the solution as it was, not as it is.

    `assess` catches a *statement* moving out from under a receipt. Nothing caught the *solution*
    moving, and after an edit the receipt has accepted something other than what is on disk. What
    makes it detectable is `repository.commit`, which schema 2 records.
    """

    def test_a_schema_one_receipt_is_skipped(self) -> None:
        """Receipts written before the commit was recorded cannot be checked, and are not guessed
        at -- reporting drift that may not exist would train people to ignore the note."""
        self.assertIsNone(ieantn.solution_drift(
            {"schema": 1, "solution": {"project": "Solutions/A.v1"}}))

    def test_a_receipt_with_no_solution_project_is_skipped(self) -> None:
        self.assertIsNone(ieantn.solution_drift(
            {"schema": 2, "repository": {"commit": "a" * 40}}))

    def test_an_unknown_commit_is_skipped(self) -> None:
        """A shallow clone, or a branch since deleted, leaves nothing to diff against."""
        self.assertIsNone(ieantn.solution_drift({
            "schema": 2,
            "repository": {"commit": "0" * 40},
            "solution": {"project": "Solutions/A.v1"},
        }))


class TestSpinoffSlicing(unittest.TestCase):
    """Turning a declaration's source range back into text that still resolves.

    The generator inlines IEANTN's own definitions into a Palomar Challenge, because a Challenge
    may not import the submitter's library. Lean supplies the ranges; these test what is done with
    them.
    """

    SOURCE = (
        "import Mathlib.Foo\n"          # 1
        "\n"                            # 2
        "namespace IEANTN\n"            # 3
        "open Real\n"                   # 4
        "\n"                            # 5
        "/-- Doc. -/\n"                 # 6
        "def Wrapper.thing (x : ℝ) : Prop :=\n"   # 7
        "  log x > 0\n"                 # 8
        "\n"                            # 9
        "end IEANTN\n"                  # 10
    )

    def _decl(self, **over):
        base = dict(name="IEANTN.Wrapper.thing", module="IEANTN.Vocabulary.X", kind="def",
                    startLine=6, startCol=0, endLine=8, endCol=12,
                    nameStartLine=7, nameStartCol=4, nameEndLine=7, nameEndCol=17)
        base.update(over)
        return base

    def test_the_slice_carries_the_docstring(self) -> None:
        """The range Lean reports starts at the docstring, which is most of why this is worth
        doing: the docstring is the informal statement a Palomar reviewer reads."""
        body, _ = ieantn.slice_source(self.SOURCE, self._decl(), "")
        self.assertTrue(body.startswith("/-- Doc. -/"))
        self.assertIn("log x > 0", body)

    def test_the_namespace_comes_from_the_written_name(self) -> None:
        """`IEANTN.Wrapper.thing` written as `Wrapper.thing` means the namespace is `IEANTN`.

        Recovering it any other way means parsing Lean; the selection range makes it arithmetic.
        """
        _, namespace = ieantn.slice_source(self.SOURCE, self._decl(), "")
        self.assertEqual(namespace, "IEANTN")

    def test_a_name_that_is_not_a_suffix_is_refused(self) -> None:
        """If the written name is not a suffix of the full name the namespace cannot be recovered.

        Guessing would produce a Challenge that compiles and states something else, which is the
        one outcome worth refusing outright.
        """
        with self.assertRaises(SystemExit):
            ieantn.slice_source(self.SOURCE, self._decl(name="Other.entirely"), "")


class TestSpinoffOpens(unittest.TestCase):
    def test_module_level_opens_are_collected(self) -> None:
        """`log x` in an inlined body means `Real.log` only because its file opened `Real`."""
        with tempfile.TemporaryDirectory() as tmp:
            f = pathlib.Path(tmp) / "X.lean"
            f.write_text(
                "import Mathlib\nopen Real ArithmeticFunction\nopen scoped Nat\n"
                "open Finset in\ndef a := 1\n-- open Commented\n",
                encoding="utf-8")
            self.assertEqual(
                ieantn.opens_of(f), ["open Real ArithmeticFunction", "open scoped Nat"])

    def test_open_in_is_excluded_and_comments_ignored(self) -> None:
        """`open X in` scopes to the next declaration, so it is already inside the sliced text."""
        with tempfile.TemporaryDirectory() as tmp:
            f = pathlib.Path(tmp) / "X.lean"
            f.write_text("open Finset in\ndef a := 1\n-- open Nope\n", encoding="utf-8")
            self.assertEqual(ieantn.opens_of(f), [])


class TestUnjustifiedLeaves(FixtureRepo):
    """What a spun-off Challenge must take as hypotheses.

    Palomar records a verified formalization; anything this network is content to accept on a
    citation's authority has to appear in the statement as an assumption rather than be silently
    absorbed.
    """

    def test_a_verified_conclusion_rests_on_nothing(self) -> None:
        self.write_node("A.v1", LITERATURE.replace("kind: literature", "kind: lean-comparator"))
        self._receipt_for("A.v1.main")
        index = ieantn.index_conclusions(ieantn.load_nodes())
        self.assertEqual(ieantn.unjustified_leaves(index, "A.v1.main"), [])

    def test_an_imported_citation_becomes_a_leaf(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node(
            "A.v1", importing("Upstream.v1").replace("kind: none-yet", "kind: lean-comparator"))
        self._receipt_for("A.v1.main")
        index = ieantn.index_conclusions(ieantn.load_nodes())
        self.assertEqual(ieantn.unjustified_leaves(index, "A.v1.main"), ["Upstream.v1.main"])

    def _receipt_for(self, key: str) -> None:
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / f"{key}.json").write_text(
            json.dumps({"conclusion": key}), encoding="utf-8")


class TestImportParsing(FixtureRepo):
    """What counts as an import, and what does not.

    Every closure check in this file is only as good as this parse. The old pattern anchored the
    module name at end of line, so a trailing comment hid an import from all of them -- silently,
    and in the direction that lets a violation through.
    """

    def test_a_trailing_comment_does_not_hide_an_import(self) -> None:
        (self.root / "IEANTN" / "Vocabulary" / "Bad.lean").write_text(
            "import Solutions.A.v1.Solution -- just for now\n", encoding="utf-8"
        )
        self.assertFalse(ieantn.check_closure())

    def test_a_commented_out_import_is_not_an_import(self) -> None:
        (self.root / "IEANTN" / "Vocabulary" / "Fine.lean").write_text(
            "-- import Solutions.A.v1.Solution\n/- import PNT.Everything -/\nimport Mathlib.Data.Nat.Defs\n",
            encoding="utf-8",
        )
        self.assertTrue(ieantn.check_closure())

    def test_a_lookalike_module_is_not_vocabulary(self) -> None:
        """`startswith` accepted `IEANTN.VocabularyScratch` as Vocabulary, and `MathlibExtras` as
        Mathlib. Nothing was ever named that way, which is precisely the problem."""
        (self.root / "IEANTN" / "Vocabulary" / "Bad.lean").write_text(
            "import IEANTN.VocabularyScratch\n", encoding="utf-8"
        )
        self.assertFalse(ieantn.check_closure())

    def test_imports_of_reads_the_module_name(self) -> None:
        target = self.root / "x.lean"
        target.write_text("import A.B -- c\nimport D\n", encoding="utf-8")
        self.assertEqual(ieantn.imports_of(target), ["A.B", "D"])


class TestGeneratedLeanIsNotInjectable(FixtureRepo):
    """Metadata strings are interpolated verbatim into the generated challenge.

    Nothing downstream reads that file critically -- CI only diffs it against what the generator
    produces -- so a crafted id would be regenerated faithfully and compiled into the core library.
    """

    def test_a_conclusion_id_must_be_an_identifier(self) -> None:
        """The crafted id is propagated to `declaration` and `challenge` too, so the consistency
        checks are satisfied and only the identifier rule can reject it."""
        crafted = "main : True := trivial\n\naxiom sneaky : False\n\ntheorem unused"
        self.write_node("A.v1", (
            f"\n- id: {json.dumps(crafted)}\n"
            f"  declaration: {json.dumps('A.v1.' + crafted)}\n"
            f"  challenge: {json.dumps('A.v1.challenge_' + crafted)}\n"
            "  imports: []\n"
            "  justifications:\n"
            "    - id: paper\n"
            "      kind: literature\n"
            "  designated: paper\n"
        ))
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        self.assertFalse(passed)
        self.assertIn("is not a Lean identifier", printed.getvalue())

    def test_an_import_reference_must_be_a_lean_name(self) -> None:
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node(
            "A.v1", importing("Upstream.v1").replace("conclusion: main", "conclusion: 'main) (h : False'")
        )
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        self.assertFalse(passed)
        self.assertIn("written verbatim into the generated challenge", printed.getvalue())

    def test_an_ordinary_id_still_passes(self) -> None:
        self.write_node("A.v1", LITERATURE.replace("main", "theorem_5_4'"))
        self.assertTrue(ieantn.check_graph())


class TestDeprecateGuards(FixtureRepo):
    def test_a_node_may_not_supersede_itself(self) -> None:
        self.write_node("A.v1", LITERATURE)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertFalse(ieantn.deprecate("A.v1", "A.v1"))

    def test_the_replacement_may_not_be_deprecated(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_node("A.v2", LITERATURE, status="deprecated")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertFalse(ieantn.deprecate("A.v1", "A.v2"))


class TestTablesFile(FixtureRepo):
    """`Tables.lean`: a node's bulk data, kept out of the file a human audits.

    Some explicit results are stated against a paper's numeric tables. Those belong beside the
    conclusions rather than inside them, because `Conclusions.lean` is the short file a reviewer
    reads and its shortness is the point -- checking three claims should not mean scrolling past
    two hundred rows to reach them.
    """

    def write_tables(self, node_id: str, body: str) -> pathlib.Path:
        directory = self.root / "IEANTN" / "Nodes" / node_id.replace(".", "/")
        directory.mkdir(parents=True, exist_ok=True)
        written = directory / "Tables.lean"
        written.write_text(body, encoding="utf-8")
        return written

    def test_conclusions_may_import_its_own_tables(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_tables("A.v1", "import IEANTN.Vocabulary\ndef t : List ℝ := [1]\n")
        directory = self.root / "IEANTN" / "Nodes" / "A" / "v1"
        (directory / "Conclusions.lean").write_text(
            "import IEANTN.Vocabulary\nimport IEANTN.Nodes.A.v1.Tables\n", encoding="utf-8")
        self.assertTrue(ieantn.check_closure())

    def test_conclusions_may_import_another_nodes_tables(self) -> None:
        """A table is data, and the node that computed it is not always the node that states a
        claim about it. Forcing a copy would create a second source of truth."""
        self.write_node("A.v1", LITERATURE)
        self.write_tables("B.v1", "import IEANTN.Vocabulary\ndef t : List ℝ := [1]\n")
        directory = self.root / "IEANTN" / "Nodes" / "A" / "v1"
        (directory / "Conclusions.lean").write_text(
            "import IEANTN.Vocabulary\nimport IEANTN.Nodes.B.v1.Tables\n", encoding="utf-8")
        self.assertTrue(ieantn.check_closure())

    def test_a_table_may_not_declare_a_theorem(self) -> None:
        """Data, not claims. A statement about a table is a conclusion, with a fingerprint and a
        justification; a proof about one belongs in a solution."""
        self.write_node("A.v1", LITERATURE)
        self.write_tables(
            "A.v1", "import IEANTN.Vocabulary\ntheorem t : True := trivial\n")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_closure()
        self.assertFalse(passed)
        self.assertIn("may not declare a `theorem`", printed.getvalue())

    def test_a_table_may_not_declare_a_lemma(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_tables("A.v1", "import IEANTN.Vocabulary\nlemma t : True := trivial\n")
        self.assertFalse(ieantn.check_closure())

    def test_a_table_may_not_import_a_conclusion(self) -> None:
        """The guidance is that a table has very few imports; the rule is that it has no claims
        upstream of it. A table needing a conclusion in order to be stated is not data."""
        self.write_node("A.v1", LITERATURE)
        self.write_tables("A.v1", "import IEANTN.Nodes.A.v1.Conclusions\ndef t : List ℝ := [1]\n")
        self.assertFalse(ieantn.check_closure())

    def test_a_table_may_not_contain_sorry(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_tables("A.v1", "import IEANTN.Vocabulary\ndef t : List ℝ := sorry\n")
        self.assertFalse(ieantn.check_closure())

    def test_the_umbrella_imports_tables(self) -> None:
        """A table no conclusion mentions yet is still data of record; leaving it out of the
        umbrella would mean nothing compiled it."""
        self.write_node("A.v1", LITERATURE)
        self.write_tables("A.v1", "import IEANTN.Vocabulary\ndef t : List ℝ := [1]\n")
        self.generate()
        umbrella = (self.root / "IEANTN" / "Nodes.lean").read_text(encoding="utf-8")
        self.assertIn("import IEANTN.Nodes.A.v1.Tables\n".replace("\n", chr(10)), umbrella)


class TestNewVersionClonesTheNode(FixtureRepo):
    """Branching a version must carry the whole node, not just its conclusions.

    Copying only `Conclusions.lean` left the new version missing `Tables.lean` and
    `Examples.lean` -- and it still compiled, because the old version's copies were there to
    satisfy the imports. It would have failed only when the old version was finally deleted.
    """

    def test_tables_and_examples_are_copied(self) -> None:
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        directory = self.write_node("A.v1", LITERATURE)
        (directory / "Tables.lean").write_text(
            "import IEANTN.Vocabulary\ndef t : List ℝ := [1]\n", encoding="utf-8")
        (directory / "Examples.lean").write_text(
            "import IEANTN.Nodes.A.v1.Conclusions\n", encoding="utf-8")
        self.assertTrue(ieantn.new_version("A"))
        fresh = self.root / "IEANTN" / "Nodes" / "A" / "v2"
        self.assertTrue((fresh / "Tables.lean").is_file(), "Tables.lean was not carried over")
        self.assertTrue((fresh / "Examples.lean").is_file(), "Examples.lean was not carried over")

    def test_the_copies_are_repointed_at_the_new_version(self) -> None:
        """`Examples.lean` imports its own node's conclusions by name, so a copy that still names
        `A.v1` would quietly demonstrate things about the version it was branched from."""
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        directory = self.write_node("A.v1", LITERATURE)
        (directory / "Examples.lean").write_text(
            "import IEANTN.Nodes.A.v1.Conclusions\n", encoding="utf-8")
        self.assertTrue(ieantn.new_version("A"))
        fresh = (self.root / "IEANTN" / "Nodes" / "A" / "v2" / "Examples.lean")
        self.assertIn("A.v2.Conclusions", fresh.read_text(encoding="utf-8"))


class TestBridgeClosure(FixtureRepo):
    """A bridge is held to the closure rule a Conclusions file is held to, and then some.

    It is the file that transports trust from one node's conclusion to another's, and unlike a
    solution it is not sandboxed and not Comparator-checked -- it is trusted because the core build
    compiles it. So it must reach nothing outside the Mathlib-only closure, and must be a proof.
    """

    def test_a_bridge_may_import_conclusions_and_mathlib(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.write_bridge(
            "import Mathlib.Data.Nat.Defs\nimport IEANTN.Nodes.A.v1.Conclusions\nimport IEANTN.Vocabulary\n"
        )
        self.assertTrue(ieantn.check_closure())

    def test_a_bridge_may_not_import_a_challenge(self) -> None:
        """The failure worth designing out: a bridge resting on the `sorry` it exists to discharge.

        It would elaborate, it would be recorded as a justification, and it would prove nothing.
        """
        self.write_node("A.v1", LITERATURE)
        self.write_bridge("import IEANTN.Nodes.A.v1.Challenge\n")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_closure()
        self.assertFalse(passed)
        self.assertIn("rest on the `sorry`", printed.getvalue())

    def test_a_bridge_may_not_import_a_solution(self) -> None:
        self.write_bridge("import Solutions.A.v1.Solution\n")
        self.assertFalse(ieantn.check_closure())

    def test_a_bridge_may_not_contain_sorry(self) -> None:
        self.write_bridge("theorem a : True := by sorry\n")
        self.assertFalse(ieantn.check_closure())

    def test_the_word_sorry_in_a_bridge_comment_is_not_a_sorry(self) -> None:
        """Same trap as for Examples: the docstring explaining the rule must not trip it."""
        self.write_bridge("/-- This bridge may not contain sorry. -/\ntheorem a : True := trivial\n")
        self.assertTrue(ieantn.check_closure())

    def test_the_bridges_umbrella_imports_every_bridge(self) -> None:
        """Generated, because a missing import is invisible: the module simply is not built."""
        self.write_bridge("theorem a : True := trivial\n")
        (self.root / "IEANTN" / "Bridges" / "Nested").mkdir()
        (self.root / "IEANTN" / "Bridges" / "Nested" / "b.lean").write_text(
            "theorem b : True := trivial\n", encoding="utf-8"
        )
        self.generate()
        umbrella = (self.root / "IEANTN" / "Bridges.lean").read_text(encoding="utf-8")
        self.assertIn("import IEANTN.Bridges.a\n", umbrella)
        self.assertIn("import IEANTN.Bridges.Nested.b\n", umbrella)


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


class TestRecordReceipt(FixtureRepo):
    """`record-receipt` writes the receipt *and* designates it.

    A Lean-verified justification rests on no citation, no external computation and no other
    version, so once one exists it is almost always what a conclusion should point at. Leaving the
    designation to a later pull request is how the first real verification landed with the graph
    reporting an unverified node moments after verifying it.
    """

    def setUp(self) -> None:
        super().setUp()
        # `record_receipt` asks Lean for fingerprints; the fixture has no Lean.
        self._real = ieantn.compute_fingerprints
        ieantn.compute_fingerprints = lambda: {  # type: ignore[assignment]
            "A.v1.main": "aa", "Upstream.v1.main": "bb"
        }
        self.addCleanup(lambda: setattr(ieantn, "compute_fingerprints", self._real))

    def test_it_writes_a_receipt_and_designates_it(self) -> None:
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        self.write_node("A.v1", LITERATURE.replace("kind: literature", "kind: none-yet"))
        self.write_comparator_config("A.v1")
        self.assertTrue(ieantn.record_receipt("A.v1", "Solutions/A.v1", "http://run", "now"))
        self.assertTrue((self.root / "receipts" / "A.v1.main.json").is_file())
        conclusion = ieantn.conclusions_of(ieantn.load_nodes()["A.v1"])[0]
        self.assertEqual(ieantn.designated_kind(conclusion), "lean-comparator")
        self.assertTrue(ieantn.check_graph(), "a designated receipt must not warn")

    def test_the_receipt_records_imported_fingerprints_too(self) -> None:
        """The graph-level property: a receipt pins what its imports said at verification time."""
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("A.v1", importing("Upstream.v1"))
        self.write_comparator_config("A.v1")
        self.assertTrue(ieantn.record_receipt("A.v1", "Solutions/A.v1", "http://run", "now"))
        receipt = json.loads(
            (self.root / "receipts" / "A.v1.main.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            sorted(receipt["statement"]), ["A.v1.main", "Upstream.v1.main"]
        )


class TestReceiptCoverage(FixtureRepo):
    """A receipt may only cover conclusions Comparator was actually asked about.

    Comparator runs once per node, against the `theorem_names` in the solution's `comparator.json`;
    receipts are written per conclusion. Nothing connected the two, so adding a second conclusion
    to an already-verified node earned it a full `lean-comparator` justification for a statement no
    verifier had ever seen. No adversary required.
    """

    def setUp(self) -> None:
        super().setUp()
        self._real = ieantn.compute_fingerprints
        ieantn.compute_fingerprints = lambda: {  # type: ignore[assignment]
            "A.v1.main": "aa", "A.v1.second": "cc", "Upstream.v1.main": "bb"
        }
        self.addCleanup(lambda: setattr(ieantn, "compute_fingerprints", self._real))

    def _two_conclusions(self) -> None:
        self.write_node(
            "A.v1",
            LITERATURE + LITERATURE.replace("id: main", "id: second")
            .replace("{node}.main", "{node}.second")
            .replace("challenge_main", "challenge_second"),
        )

    def test_a_conclusion_comparator_never_saw_gets_no_receipt(self) -> None:
        self._two_conclusions()
        self.write_comparator_config("A.v1", ["A.v1.challenge_main"])
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            recorded = ieantn.record_receipt("A.v1", "Solutions/A.v1", "http://run", "now")
        self.assertFalse(recorded)
        self.assertIn("A.v1.challenge_second", printed.getvalue())
        self.assertFalse((self.root / "receipts").exists())

    def test_a_missing_config_is_refused(self) -> None:
        self.write_node("A.v1", LITERATURE)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertFalse(ieantn.record_receipt("A.v1", "Solutions/A.v1", "http://run", "now"))
        self.assertIn("does not exist", printed.getvalue())

    def test_the_receipt_records_what_pinned_the_verification(self) -> None:
        """ARCHITECTURE says "what pins a verification is the commit its receipt records", and says
        the receipt carries the four tool revisions. Neither was true until the docs audit checked.

        Both matter for the same reason: without them a receipt says a verification happened but
        not what tree it ran against or what checked it, and "re-run at the recorded pin" has no
        referent."""
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        self.write_node("A.v1", LITERATURE)
        self.write_comparator_config("A.v1")
        (self.root / "scripts").mkdir(exist_ok=True)
        (self.root / "scripts" / "verify-comparator.sh").write_text(
            "comparator_commit=aaa\nlean4export_commit=bbb\n"
            "lean4export_toolchain=leanprover/lean4:v4.34.0-rc2\n"
            "landrun_commit=ccc\nnanoda_commit=ddd\n",
            encoding="utf-8",
        )
        self.assertTrue(ieantn.record_receipt("A.v1", "Solutions/A.v1", "http://run", "now"))
        receipt = json.loads(
            (self.root / "receipts" / "A.v1.main.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            receipt["tools"],
            {"comparator": "aaa", "lean4export": "bbb", "landrun": "ccc", "nanoda": "ddd"},
        )
        self.assertIn("commit", receipt["repository"])

    def test_full_coverage_is_accepted(self) -> None:
        try:
            import ruamel.yaml  # noqa: F401
        except ImportError:
            self.skipTest("ruamel.yaml not installed")
        self._two_conclusions()
        self.write_comparator_config("A.v1")
        self.assertTrue(ieantn.record_receipt("A.v1", "Solutions/A.v1", "http://run", "now"))
        self.assertTrue((self.root / "receipts" / "A.v1.second.json").is_file())


class TestProvenanceCannotBeBypassed(FixtureRepo):
    """The whole check rests on the run being in *this* repository.

    Anyone can stand up a repository with a `verify.yml` whose jobs succeed, so "the run exists and
    succeeded" is worth nothing on its own. The repository is identified from `git remote get-url
    origin` -- and when that could not be determined, the check used to go and ask the repository
    the receipt named, which made it bypassable by deleting a remote.
    """

    def _receipt(self, key: str, url: str) -> None:
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / f"{key}.json").write_text(
            json.dumps({"conclusion": key, "run": {"workflow_run": url}}), encoding="utf-8"
        )

    def test_an_unknown_repository_is_refused_online(self) -> None:
        self._receipt("A.v1.main", "https://github.com/attacker/lookalike/actions/runs/1")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_receipts(online=True)
        self.assertFalse(passed, "with no origin remote, provenance must refuse, not go and ask")
        self.assertIn("cannot determine this repository", printed.getvalue())

    def test_offline_still_checks_only_shape(self) -> None:
        """Offline the check stays useful without a network, so it does not need the remote."""
        self._receipt("A.v1.main", "https://github.com/attacker/lookalike/actions/runs/1")
        self.assertTrue(ieantn.check_receipts(online=False))

    def test_no_receipts_means_nothing_to_refuse(self) -> None:
        self.assertTrue(ieantn.check_receipts(online=True))


class TestReceiptProvenance(FixtureRepo):
    """A receipt must name a real, successful run of the verification workflow.

    This is the enforcement that replaced the intended `receipts/` path ruleset, which GitHub
    refuses on a public repository and on any repository not owned by an organisation. It is the
    better control anyway: a path rule says who wrote the file, while this says the verification
    happened -- and a commit author is trivially forged where a successful `verify.yml` run,
    gated on a maintainer approving an environment, is not.

    Only the offline half is tested here; the online half needs the network.
    """

    def _receipt(self, url: str) -> None:
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / "A.v1.main.json").write_text(
            json.dumps({"conclusion": "A.v1.main", "run": {"workflow_run": url}}),
            encoding="utf-8",
        )

    def test_a_receipt_with_no_run_url_fails(self) -> None:
        self._receipt("")
        self.assertFalse(ieantn.check_receipts(online=False))

    def test_a_receipt_with_a_non_run_url_fails(self) -> None:
        self._receipt("https://example.invalid/trust-me")
        self.assertFalse(ieantn.check_receipts(online=False))

    def test_a_well_formed_run_url_passes_offline(self) -> None:
        self._receipt("https://github.com/teorth/IEANTN/actions/runs/123")
        self.assertTrue(ieantn.check_receipts(online=False))

    def test_no_receipts_is_not_a_failure(self) -> None:
        self.assertTrue(ieantn.check_receipts(online=False))


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
