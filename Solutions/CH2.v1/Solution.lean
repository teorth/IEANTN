/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section9Cor13
import IEANTN.Nodes.CH2.v1.Conclusions
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions

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

§6 through §9 and Appendix B are now done as well, and **Corollary 1.2 is closed**: both of its
displays are proved below from this node's imports, with no `sorry` between them and Mathlib.

| file | content |
|---|---|
| `Section6*`, `ZetaReal01` | §6 — the residues, the zero terms, the contour, `svm_abs_bound` |
| `Section7*` | §7 — `prop:vihuela`, the bound on the `ω⁺` zero sum |
| `Section81*` | §8.1 — `prop:titch96A`, `lem:saghar`, `lem:hardin` |
| `Section9`, `Section9Limit` | §9 — `prop:sagaro`, and Corollary 1.2 at `σ = 0` and `σ = 1` |

## What is missing

Corollary 1.3's `∑ Λ(n)/n` display. Its `ψ` display is now proved (`Section9Cor13`), by Corollary
1.2 at `T = 3 · 10¹² + 5` for `x` above that, at `T = 10⁷` down to `x > 10⁹`, `Buthe.v1` on
`11 < x ≤ 10⁹` and a trivial bound below `11`. What is left is the same descent for the sum, which
goes by Abel summation against the `ψ` bound.
-/

theorem CH2.v1.challenge_corollary_1_2_psi
    (gammaasymptotics_v2_digamma_sub_log_isbigo_strip : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (cotangentseries_v1_cot_series_zeta_values : CotangentSeries.v1.cot_series_zeta_values)
    (zerocount_v1_rvm_error_bound : ZeroCount.v1.rvm_error_bound)
    (zerocount_v1_rvm_error_small : ZeroCount.v1.rvm_error_small)
    (zetalogderiv_v1_logderiv_functional_equation : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (zetalogderivvalues_v1_logderiv_two : ZetaLogDerivValues.v1.logDeriv_two)
    (zetalogderivvalues_v1_logderiv_three_halves : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (zetalogderivvalues_v1_logderiv_neg_one : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (zetalogderivvalues_v1_logderiv_laurent_alternating : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (zetahadamard_v1_logderiv_partial_fractions : ZetaHadamard.v1.logDeriv_partial_fractions)
    (plattzerosum_v1_inv_ordinate_sum_le : PlattZeroSum.v1.inv_ordinate_sum_le) :
    CH2.v1.corollary_1_2_psi :=
  CH2Section9.corollary_1_2_psi zetalogderiv_v1_logderiv_functional_equation
    gammaasymptotics_v2_digamma_sub_log_isbigo_strip
    zetalogderivvalues_v1_logderiv_laurent_alternating zetalogderivvalues_v1_logderiv_neg_one
    zetalogderivvalues_v1_logderiv_two zetalogderivvalues_v1_logderiv_three_halves
    cotangentseries_v1_cot_series_zeta_values zerocount_v1_rvm_error_bound
    zerocount_v1_rvm_error_small plattzerosum_v1_inv_ordinate_sum_le
    zetahadamard_v1_logderiv_partial_fractions

theorem CH2.v1.challenge_corollary_1_2_lambda_sum
    (gammaasymptotics_v2_digamma_sub_log_isbigo_strip : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (cotangentseries_v1_cot_series_zeta_values : CotangentSeries.v1.cot_series_zeta_values)
    (zerocount_v1_rvm_error_bound : ZeroCount.v1.rvm_error_bound)
    (zerocount_v1_rvm_error_small : ZeroCount.v1.rvm_error_small)
    (zetalogderiv_v1_logderiv_functional_equation : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (zetalogderivvalues_v1_logderiv_two : ZetaLogDerivValues.v1.logDeriv_two)
    (zetalogderivvalues_v1_logderiv_three_halves : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (zetalogderivvalues_v1_logderiv_neg_one : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (zetalogderivvalues_v1_logderiv_laurent_alternating : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (zetahadamard_v1_logderiv_partial_fractions : ZetaHadamard.v1.logDeriv_partial_fractions)
    (plattzerosum_v1_inv_ordinate_sum_le : PlattZeroSum.v1.inv_ordinate_sum_le) :
    CH2.v1.corollary_1_2_lambda_sum :=
  CH2Section9.corollary_1_2_lambda_sum zetalogderiv_v1_logderiv_functional_equation
    gammaasymptotics_v2_digamma_sub_log_isbigo_strip
    zetalogderivvalues_v1_logderiv_laurent_alternating zetalogderivvalues_v1_logderiv_neg_one
    zetalogderivvalues_v1_logderiv_two zetalogderivvalues_v1_logderiv_three_halves
    cotangentseries_v1_cot_series_zeta_values zerocount_v1_rvm_error_bound
    zerocount_v1_rvm_error_small plattzerosum_v1_inv_ordinate_sum_le
    zetahadamard_v1_logderiv_partial_fractions

theorem CH2.v1.challenge_corollary_1_3_psi
    (ch2_v1_corollary_1_2_psi : CH2.v1.corollary_1_2_psi)
    (platttrudgian_v1_rh_up_to_exact : PlattTrudgian.v1.rh_up_to_exact)
    (buthe_v1_theorem_2_psi : Buthe.v1.theorem_2_psi) :
    CH2.v1.corollary_1_3_psi :=
  CH2Section9.corollary_1_3_psi ch2_v1_corollary_1_2_psi platttrudgian_v1_rh_up_to_exact
    buthe_v1_theorem_2_psi

theorem CH2.v1.challenge_corollary_1_3_lambda_sum
    (ch2_v1_corollary_1_2_lambda_sum : CH2.v1.corollary_1_2_lambda_sum)
    (platttrudgian_v1_rh_up_to_exact : PlattTrudgian.v1.rh_up_to_exact)
    (buthe_v1_theorem_2_psi : Buthe.v1.theorem_2_psi) :
    CH2.v1.corollary_1_3_lambda_sum := by
  sorry
