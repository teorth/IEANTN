/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section5
import IEANTN.Nodes.CH2.v1.Conclusions
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions
import IEANTN.Nodes.GammaAsymptotics.v1.Conclusions

/-!
# Solution: `CH2.v1` — **incomplete, and deliberately so**

This solution is being built in stages, roughly a paper section at a time. See `progress.yaml`
for what is closed and what is not; `python scripts/ieantn.py progress CH2.v1` reports the hole
count.

**Every `sorry` below is a hole to be filled, not a permanent one.** That is the opposite of the
convention in a `Challenge.lean`, where a `sorry` is correct and permanent. A solution with any
`sorry` cannot be verified — Comparator is all-or-nothing per node — so none of these conclusions
will go green until all four are closed.

## What is already here

Sections 2 through 5 of Chirre–Helfgott, ported from `PrimeNumberTheoremAnd` where they are proved
free of `sorry`:

| file | content |
|---|---|
| `AdditiveCombination`, `RectanglePort`, `ResiduePort` | rectangle contour machinery |
| `PntSupport` … `WienerPort` | the Fourier and Sobolev support the above needs |
| `Part1Fourier` | §2, the Fourier-analytic core — Propositions 2.3 and 2.4 |
| `Approximants`, `Decay` | §4 as replaced by the addendum, the extremal approximants |
| `ZetaConjPort` | conjugation symmetry of `ζ` |
| `Section5` | §5 — Lemma 5.1 and Proposition 5.2, the contour shift |

The bespoke vocabulary those carry — `LadderParams`, `Phi_lambda`, `sumResiduesIn` and the rest —
lives here in the solution and **never reaches `IEANTN/Vocabulary/` or any `Conclusions.lean`**.
That is the point of putting it here: §5 is machinery internal to the paper, not one of its
exports, so it does not belong in the layer the network reads.

## What is missing

§6 through §8, and Appendix B. Nobody has formalized them — `PrimeNumberTheoremAnd`'s `CH2.lean`
carries exactly four `sorry`s, and they are exactly these four corollaries, with
`TODO: incorporate material from [CH2, Section 6]` and `[CH2, Section 7] onwards` where the work
would go. So this is not a port waiting to be finished; it is mathematics waiting to be done.

The inputs that will close it are recorded as this node's imports rather than proved here:
`CH2.v2` (Proposition 2.4, verified), `CH2.v3` (the approximants, verified), `ZeroCount.v1`
(Rosser's zero count, for the constant `C_T`), and for Corollary 1.3 `PlattTrudgian.v1` together
with a numerics node that does not exist yet.
-/

theorem CH2.v1.challenge_corollary_1_2_psi
    (gammaasymptotics_v1_digamma_sub_log_isbigo :
      GammaAsymptotics.v1.digamma_sub_log_isBigO) :
    CH2.v1.corollary_1_2_psi := by
  sorry

theorem CH2.v1.challenge_corollary_1_2_lambda_sum
    (gammaasymptotics_v1_digamma_sub_log_isbigo :
      GammaAsymptotics.v1.digamma_sub_log_isBigO) :
    CH2.v1.corollary_1_2_lambda_sum := by
  sorry

theorem CH2.v1.challenge_corollary_1_3_psi
    (ch2_v1_corollary_1_2_psi : CH2.v1.corollary_1_2_psi)
    (platttrudgian_v1_rh_up_to : PlattTrudgian.v1.rh_up_to) :
    CH2.v1.corollary_1_3_psi := by
  sorry

theorem CH2.v1.challenge_corollary_1_3_lambda_sum
    (ch2_v1_corollary_1_2_lambda_sum : CH2.v1.corollary_1_2_lambda_sum)
    (platttrudgian_v1_rh_up_to : PlattTrudgian.v1.rh_up_to) :
    CH2.v1.corollary_1_3_lambda_sum := by
  sorry
