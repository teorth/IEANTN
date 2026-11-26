#!/usr/bin/env python3
"""A conclusion that is in the literature and false as stated.

Issues 260 and 268. Büthe's Lemma 3 defines `A = π(a) − li(a) + (a − θ(a))/log a`, carries
`+ A log x/√x` in both of its displayed bounds, and checks `A(10) > 0.1` in its proof. The
identity the proof rests on, (6.17), is correct as printed and gives `− A`, so two of the
network's conclusions transcribe the paper faithfully and are false:

* `ButheNumerics.v1.lemma_3_constant_gt_at_10` — `0.1 < −0.1449`;
* `Buthe.v2.lemma_3_bounds` — the upper conjunct, refuted at `a = 3·10⁶`.

Both stay in the network. The claim a node makes is *about the literature*, and a published lemma
that is false as printed is a fact about the literature worth recording; deleting it would make
the graph disagree with the papers it indexes. What must not happen is for the views to go on
offering such a statement as evidence, or for the queue to send someone after a proof of it.
"""
from __future__ import annotations

import contextlib
import importlib.util
import io
import pathlib
import unittest

_SPEC = importlib.util.spec_from_file_location(
    "ieantn", pathlib.Path(__file__).resolve().parent.parent / "scripts" / "ieantn.py"
)
assert _SPEC and _SPEC.loader
ieantn = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(ieantn)

REFUTED = ("ButheNumerics.v1.lemma_3_constant_gt_at_10", "Buthe.v2.lemma_3_bounds")


def conclusion(key: str) -> dict:
    node_id, _, cid = key.rpartition(".")
    node = ieantn.load_nodes()[node_id]
    return next(c for c in ieantn.conclusions_of(node) if c.get("id") == cid)


class TestTheTwoRefutationsAreRecorded(unittest.TestCase):
    def test_both_carry_a_counterexample_and_an_issue(self) -> None:
        for key in REFUTED:
            with self.subTest(conclusion=key):
                refuted = conclusion(key).get("refuted") or {}
                self.assertTrue(refuted, f"{key} should carry a `refuted` block")
                self.assertTrue(str(refuted.get("counterexample") or "").strip())
                self.assertIsInstance(refuted.get("issue"), int)

    def test_the_counterexamples_name_the_numbers(self) -> None:
        """A refutation nobody can check is worth no more than the claim it withdraws."""
        self.assertIn(
            "-0.1448739805",
            conclusion("ButheNumerics.v1.lemma_3_constant_gt_at_10")["refuted"]["counterexample"])
        bounds = conclusion("Buthe.v2.lemma_3_bounds")["refuted"]["counterexample"]
        for piece in ("3*10^6", "1.70040709", "1.72994393"):
            self.assertIn(piece, bounds)


class TestARefutationOverridesTheEvidence(unittest.TestCase):
    def test_display_kind_is_refuted_whatever_is_designated(self) -> None:
        """`lemma_3_constant_gt_at_10` designates a `numerical` justification, and a view that
        reported `computation` for a statement known to be false would be the one thing these
        files exist to prevent."""
        key = "ButheNumerics.v1.lemma_3_constant_gt_at_10"
        self.assertEqual(ieantn.designated_kind(conclusion(key)), "numerical")
        self.assertEqual(ieantn.display_kind(key, conclusion(key)), ieantn.REFUTED_KIND)

    def test_refuted_is_the_weakest_evidence_there_is(self) -> None:
        """Weaker than `none-yet`: an unjustified conclusion might still be true."""
        self.assertEqual(ieantn.EVIDENCE_ORDER[0], ieantn.REFUTED_KIND)

    def test_a_refuted_conclusion_drags_its_node_down(self) -> None:
        """A node is summarised by its weakest conclusion, which is the point of that rule."""
        nodes = ieantn.load_nodes()
        for node_id in ("ButheNumerics.v1", "Buthe.v2"):
            with self.subTest(node=node_id):
                self.assertEqual(
                    ieantn.weakest_kind(node_id, ieantn.conclusions_of(nodes[node_id])),
                    ieantn.REFUTED_KIND)

    def test_it_has_something_to_draw_itself_with(self) -> None:
        self.assertIn(ieantn.REFUTED_KIND, ieantn.EVIDENCE_STYLE)


class TestTheQueueAsksForRerouting(unittest.TestCase):
    """Nothing forces a refuted conclusion out of the network; the record is the point. What is
    queued is the work it creates for the consumers that still route through it."""

    def setUp(self) -> None:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            ieantn.housekeeping()
        self.printed = out.getvalue()

    def test_each_consumer_is_named(self) -> None:
        self.assertIn("reroute   Buthe.v1.theorem_2_li_gt_pi  off refuted "
                      "ButheNumerics.v1.lemma_3_constant_gt_at_10", self.printed)
        self.assertIn("reroute   Buthe.v1.theorem_2_li_minus_pi  off refuted "
                      "Buthe.v2.lemma_3_bounds", self.printed)

    def test_a_corrected_version_is_asked_for_while_none_exists(self) -> None:
        """Until one exists there is nowhere to send the consumers."""
        for key in REFUTED:
            with self.subTest(conclusion=key):
                self.assertIn(f"restate   {key}  (refuted, no corrected version yet)",
                              self.printed)


class TestCheckRefusesAnIncoherentRefutation(unittest.TestCase):
    """`check`'s validation of the `refuted` block is exercised against synthetic nodes in
    `test_ieantn.TestRefutedConclusions`; this only pins the vocabulary."""

    def test_the_allowed_keys_are_closed(self) -> None:
        self.assertEqual(ieantn.REFUTED_KEYS,
                         {"issue", "counterexample", "note", "corrected"})


if __name__ == "__main__":
    unittest.main()
