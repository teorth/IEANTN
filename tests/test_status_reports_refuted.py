#!/usr/bin/env python3
"""`status` must say a refuted conclusion is false, not merely unverified.

`display_kind` has known about `refuted` since #269, and `report`, `diff`, `housekeeping` and the
graph styling were all wired through it. `status` was not: it read `designated_kind` directly, so a
conclusion with a recorded counterexample printed as

    -       ButheNumerics.v1.lemma_3_constant_gt_at_10
            not Lean-verified here; designated `numerical`

which reads as "cited, nobody checked it" when the truth is "somebody checked it and it is false".
`status` is the command CLAUDE.md lists for exactly this question, so that was the one view where
the omission mattered most.
"""
from __future__ import annotations

import contextlib
import io
import unittest
import unittest.mock

from test_ieantn import LITERATURE, REFUTED, FixtureRepo, ieantn, refuted_with


def run_status() -> str:
    printed = io.StringIO()
    with contextlib.redirect_stdout(printed), unittest.mock.patch.object(
        ieantn, "compute_fingerprints", return_value={}
    ):
        ieantn.status()
    return printed.getvalue()


class TestStatusReportsRefuted(FixtureRepo):
    def test_a_refuted_conclusion_is_not_reported_as_merely_unverified(self) -> None:
        self.write_node("A.v1", REFUTED)
        printed = run_status()
        self.assertIn("refuted A.v1.main", printed)
        self.assertIn("false as stated", printed)
        # The regression: it must not be filed under its designated kind, which is `literature`
        # in this fixture and would print as though nobody had checked it.
        self.assertNotIn("not Lean-verified here; designated", printed)

    def test_the_issue_is_named(self) -> None:
        """A counterexample nobody can find again is not much use."""
        self.write_node("A.v1", REFUTED)
        self.assertIn("#260", run_status())

    def test_it_says_when_there_is_no_corrected_version(self) -> None:
        self.write_node("A.v1", REFUTED)
        printed = run_status()
        self.assertIn("No corrected version yet", printed)
        self.assertNotIn("Corrected by", printed)

    def test_it_names_the_corrected_version_when_there_is_one(self) -> None:
        self.write_node("B.v1", LITERATURE)
        self.write_node("A.v1", refuted_with("""
            issue: 260
            counterexample: The left side evaluates to -0.1449.
            corrected: B.v1.main
        """))
        printed = run_status()
        self.assertIn("Corrected by `B.v1.main`", printed)
        self.assertNotIn("No corrected version yet", printed)

    def test_the_totals_line_counts_it_separately(self) -> None:
        """Counting it under `-` would hide it among the merely uncertified."""
        self.write_node("A.v1", REFUTED)
        self.assertIn("refuted: 1", run_status())

    def test_the_explanation_says_why_it_stays_in_the_network(self) -> None:
        self.write_node("A.v1", REFUTED)
        printed = run_status()
        self.assertIn("supports nothing downstream", printed)
        self.assertIn("stays in the network on purpose", printed)

    def test_an_ordinary_conclusion_is_untouched(self) -> None:
        """The new branch must not swallow the existing report."""
        self.write_node("A.v1", LITERATURE)
        printed = run_status()
        self.assertIn("not Lean-verified here; designated `literature`", printed)
        self.assertNotIn("refuted", printed)


class TestTheCommittedNetwork(unittest.TestCase):
    def test_every_refuted_conclusion_displays_as_refuted(self) -> None:
        """The case this exists for, against the real network rather than a fixture."""
        nodes = ieantn.load_nodes()
        conclusions = {
            f"{node_id}.{c.get('id')}": c
            for node_id, node in nodes.items()
            for c in ieantn.conclusions_of(node)
        }
        refuted = {k for k, c in conclusions.items() if c.get("refuted")}
        self.assertTrue(refuted, "the network has no refuted conclusion to check")
        for key in sorted(refuted):
            with self.subTest(conclusion=key):
                self.assertEqual(
                    ieantn.display_kind(key, conclusions[key]), ieantn.REFUTED_KIND
                )


if __name__ == "__main__":
    unittest.main()
