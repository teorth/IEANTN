/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import PsiToTheta
import Dawson
import IEANTN.Nodes.Buthe.v1.Conclusions
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions

/-!
# From a bound on `Eθ` to one on `Eπ`, and the headline estimate

The paper's Lemma 12, Theorem 3, Corollary 23 and Corollary 26.

The conversion is partial summation: `π(x) - Li(x)` is an integral of `(θ(t) - t)/(t log² t)` plus
a boundary term, so an admissible bound for `Eθ` integrates to one for `Eπ`. The work is in
bounding that integral without losing the shape, which is `integral_theta_bound`.

## Theorem 3 needs a second threshold, and an earlier draft of this file got that wrong

The conclusion is **not** an admissible bound from `x₀` onwards. The paper's (def-x1) introduces

`x₁ ≥ max{x₀, exp((1 + C/(2√R))²)}`

and concludes for `x ≥ x₁` only. An earlier version of this file stated the conclusion at `x₀`,
which claims strictly more than the paper proves. The same draft replaced the paper's explicit
`A_π = (1 + μ_asymp(x₀, x₁)) A_θ` with `∃ Aπ`, which throws away the constant the corollaries need.
Both are recorded here because the file typechecked in that state: a statement can be wrong in
shape and still compile.

## Where the two kinds of input enter

`Buthe.v1.theorem_2_li_minus_pi` supplies the mid-range, below `10¹⁹`, where the asymptotic bound
is not yet the best thing available.

`FKS2Numerics.v1.table6_row2_floor` supplies the small range `[e, e⁶]`, where the claim is a finite
check rather than analysis. **Upstream carries that as a `sorry`; here it is a hypothesis**, which
is the whole reason the numerical content was split into its own node.
-/

namespace FKS2Sol

open Real IEANTN

/-- `m(x₀, x) = max((log x₀)^{(2B-3)/2}, (log x)^{(2B-3)/2})`, the paper's (alpha_def).

It is a `max` rather than an evaluation because the exponent `(2B-3)/2` changes sign with `B`: the
substituted integrand `u^{2B-3}` is increasing for `B > 3/2` and decreasing for `B < 3/2`, so
neither endpoint dominates in general. -/
noncomputable def mFactor (B x₀ x : ℝ) : ℝ :=
  max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2))

/-- `∫₀^v e^{s²} ds = e^{v²} D₊(v)`: the Dawson function is exactly this integral, rescaled.

This is the bridge that puts the substituted integral in terms of `D₊`. After `u = √(log t)` and
completing the square in `u² - Cu/√R`, what is left is an integral of `e^{s²}`, and this turns it
into the `D₊` the paper's bound is written with. -/
theorem integral_exp_sq_eq (v : ℝ) :
    (∫ s in (0 : ℝ)..v, exp (s ^ 2)) = exp (v ^ 2) * dawson v := by
  unfold dawson
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- `(log t)^{(2B-3)/2} ≤ mFactor B x₀ x` throughout `[x₀, x]`.

This is why `mFactor` is a `max` rather than an evaluation: the exponent changes sign with `B`, so
for `B > 3/2` the bound is attained at `x` and for `B < 3/2` at `x₀`, and neither endpoint dominates
in general. It is the step where the paper says "note that `u^{2B-3} ≤ m(x₀,x)`". -/
theorem rpow_log_le_mFactor {B x₀ x t : ℝ} (h₀ : 1 < x₀) (ht₀ : x₀ ≤ t) (htx : t ≤ x) :
    (log t) ^ ((2 * B - 3) / 2) ≤ mFactor B x₀ x := by
  have hl₀ : 0 < log x₀ := log_pos h₀
  have hlt : log x₀ ≤ log t := log_le_log (by linarith) ht₀
  have hltx : log t ≤ log x := log_le_log (by linarith) htx
  unfold mFactor
  rcases le_or_gt 0 ((2 * B - 3) / 2) with hr | hr
  · exact le_max_of_le_right (rpow_le_rpow (by linarith) hltx hr)
  · exact le_max_of_le_left (rpow_le_rpow_of_nonpos hl₀ hlt hr.le)

/-- **Lemma 12.** The integral partial summation produces, bounded via the Dawson function.

This is the analytic heart of the `θ → π` step. Substituting `u = √(log t)` turns the integral of
the admissible bound into `∫ u^{2B-3} exp(u² - Cu/√R) du`; bounding `u^{2B-3}` by `mFactor` leaves
a Dawson integral, which is where `D₊` enters.

The remaining argument, in the paper's order and with the two pieces above in place:

1. bound the integrand by the admissible bound, giving `(Aθ/R^B) ∫ (log t)^{B-2} e^{-C√(log t/R)}`;
2. substitute `t = e^{u²}`, `dt = 2u e^{u²} du`, giving `2(Aθ/R^B) ∫ u^{2B-3} e^{u² - Cu/√R} du`;
3. replace `u^{2B-3}` by `mFactor` — `rpow_log_le_mFactor`;
4. complete the square, `u² - Cu/√R = (u - C/(2√R))² - C²/(4R)`;
5. evaluate with `integral_exp_sq_eq` and drop the lower endpoint, which is nonnegative.

Step 5's exponentials collapse: `e^{-C²/(4R)} e^{(√(log x) - C/(2√R))²} = x e^{-C√(log x/R)}`, which
is where the `x` in the statement comes from. Only step 2 needs machinery not already here. -/
theorem integral_theta_bound {Aθ B C R x₀ : ℝ} (hR : 0 < R) (hx₀ : 1 < x₀)
    (h : HasClassicalBound Eθ Aθ B C R x₀) {x : ℝ} (hx : x₀ ≤ x) :
    (∫ t in x₀..x, |Chebyshev.theta t - t| / (t * (log t) ^ 2)) ≤
      2 * Aθ / R ^ B * x * mFactor B x₀ x * exp (-C * sqrt (log x / R)) *
        dawson (sqrt (log x) - C / (2 * sqrt R)) := by
  sorry

/-- **Theorem 3**, the general `θ → π` conversion, stated as the paper does.

Three things are load-bearing and easy to lose:

* the conclusion starts at `x₁`, not `x₀` — see the module docstring;
* `A_π` is explicit, `(1 + μ_asymp(x₀, x₁)) A_θ`;
* `B ≥ max(3/2, 1 + C²/(16R))` is `Growth.lean`'s Corollary 11 hypothesis, which is what makes the
  resulting bound decreasing and so lets a single evaluation at `x₁` extend upward. -/
noncomputable def muAsymp (Aθ B C R x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * log x₀) *
      |(primeCounting x₀ - Li x₀) / (x₀ / log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|
    + 2 * dawson (sqrt (log x₁) - C / (2 * sqrt R)) / sqrt (log x₁)

theorem classicalBound_pi_of_theta
    {Aθ B C R x₀ x₁ : ℝ} (hR : 0 < R) (hB : max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B) (hx₀ : 1 < x₀)
    (hx₁ : max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)) ≤ x₁)
    (h : HasClassicalBound Eθ Aθ B C R x₀) :
    HasClassicalBound Eπ ((1 + muAsymp Aθ B C R x₀ x₁) * Aθ) B C R x₁ := by
  sorry

/-- **Corollary 23**, at the row this node states: `Eπ` obeys the classical bound with
`A = 0.826`, `B = 1/4`, `C = 1`, `R = 5.5666305`, for all `x ≥ e`.

Three ranges, and only the first is analysis. Above `10¹⁹` the conversion of Theorem 3 applied to
Corollary 14. Between `e⁶` and `10¹⁹`, Büthe's estimate. On `[e, e⁶]`, the finite check — the
threshold `x₀ = e` is exactly where that check runs out. -/
theorem corollary_23
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi)
    (hfloor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_23 := by
  sorry

/-- **Corollary 26**, the paper's headline: `|π(x) - Li(x)| ≤ 0.4298 x / log x` for all `x ≥ 2`.

Split at `e`. For `x ≥ e` this is Corollary 23 with the admissible bound compared against the
constant — the bound's maximum on `[e, ∞)` is below `0.4298`. For `2 ≤ x < e` it is direct:
`π(x) = 1`, `0 ≤ Li(x) ≤ 2`, and `log x / x ≤ 1/e`. No new input is needed for the small piece,
which is why this conclusion imports nothing that Corollary 23 does not. -/
theorem corollary_26
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi) :
    FKS2.v1.corollary_26 := by
  sorry

end FKS2Sol
