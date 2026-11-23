#!/usr/bin/env python3
"""A `numerical` justification on a statement that is really one closed inequality.

Issue 260: `ButheNumerics.v1.lemma_3_constant_gt_at_10` asserted

    0.1 < primeCounting 10 - li 10 + (10 - Chebyshev.theta 10) / Real.log 10

where the right-hand side is `-0.1448739805`. It was **false**, not vacuous, and no part of the
toolchain could see it: `check` looks at shape, closure, acyclicity and receipt provenance, none
of which evaluate an inequality, and `housekeeping` queues work by designated kind, where
`numerical` counts as justified and so is never queued.

`point_evaluation` is the narrow syntactic test that separates a closed evaluation -- which a
Lean proof could settle, and which therefore belongs in the queue -- from the large searches
`numerical` is meant for. These tests pin both directions, because a queue of tasks nobody can
action is the failure mode this report has already been through once.
"""
from __future__ import annotations

import importlib.util
import pathlib
import unittest

_SPEC = importlib.util.spec_from_file_location(
    "ieantn", pathlib.Path(__file__).resolve().parent.parent / "scripts" / "ieantn.py"
)
assert _SPEC and _SPEC.loader
ieantn = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(ieantn)


def statement(node_id: str, cid: str) -> str:
    """The Lean source of one conclusion, as `housekeeping` reads it."""
    return ieantn.read_declaration(node_id, cid)[1]


class TestPointEvaluationRecognisesClosedArithmetic(unittest.TestCase):
    def test_the_false_buthe_constant_is_a_point_evaluation(self) -> None:
        """The statement issue 260 is about. This is the case the test exists for."""
        source = statement("ButheNumerics.v1", "lemma_3_constant_gt_at_10")
        self.assertIn("primeCounting 10", source)
        self.assertTrue(ieantn.point_evaluation(source))

    def test_its_true_sibling_is_too(self) -> None:
        """`A(1500) <= 0` is true, and equally provable. Both belong in the queue."""
        self.assertTrue(
            ieantn.point_evaluation(statement("ButheNumerics.v1", "lemma_3_constant_nonpos"))
        )

    def test_a_rescaling_norm_num_would_close(self) -> None:
        self.assertTrue(
            ieantn.point_evaluation(statement("FKS.v1", "rescaled_C_is_short_of_two"))
        )


class TestPointEvaluationExcludesRealComputations(unittest.TestCase):
    """The exclusions matter as much as the inclusions: each of these is `numerical` correctly."""

    def test_a_predicate_hiding_an_exhaustive_search(self) -> None:
        """`RiemannHypothesisUpTo (10 ^ 11)` quantifies inside its own definition."""
        source = statement("FKBJ.v1", "rh_up_to")
        self.assertIn("RiemannHypothesisUpTo", source)
        self.assertFalse(ieantn.point_evaluation(source))

    def test_a_goldbach_verification(self) -> None:
        self.assertFalse(ieantn.point_evaluation(statement("OliveiraESilva2014.v1",
                                                           "even_up_to_4e18")))

    def test_a_claim_about_a_set_of_zeros(self) -> None:
        """Ranging over a set is not a point evaluation, even written as an equation."""
        source = statement("LowZeroes.v1", "no_zeroes_below_first_ordinate")
        self.assertIn("Set.Ioo", source)
        self.assertFalse(ieantn.point_evaluation(source))

    def test_a_quantified_bound(self) -> None:
        self.assertFalse(ieantn.point_evaluation(statement("Buthe.v2", "lemma_3_bounds")))

    def test_a_body_that_could_not_be_read(self) -> None:
        self.assertFalse(ieantn.point_evaluation(""))
        self.assertFalse(ieantn.point_evaluation("def thing : Prop :="))


class TestTheQueueNamesThem(unittest.TestCase):
    def test_housekeeping_queues_the_false_conclusion(self) -> None:
        """The regression that matters: before this, nothing in the tooling mentioned it."""
        import contextlib
        import io

        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            ieantn.housekeeping()
        printed = out.getvalue()
        self.assertIn("prove     ButheNumerics.v1.lemma_3_constant_gt_at_10", printed)
        self.assertIn("a closed evaluation Lean can settle", printed)

    def test_every_queued_statement_really_is_closed(self) -> None:
        """A property, so the queue cannot fill up with tasks nobody can action."""
        for node_id, node in ieantn.load_nodes().items():
            for conclusion in ieantn.conclusions_of(node):
                cid = conclusion.get("id")
                if ieantn.designated_kind(conclusion) != "numerical":
                    continue
                source = statement(node_id, cid)
                if not ieantn.point_evaluation(source):
                    continue
                body = source.partition(":=")[2]
                with self.subTest(conclusion=f"{node_id}.{cid}"):
                    self.assertNotIn("∀", body)
                    self.assertNotIn("∃", body)
                    self.assertNotIn("Set", ieantn.LEAN_NAME_RE.findall(body))


if __name__ == "__main__":
    unittest.main()
