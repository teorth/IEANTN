/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Stieltjes
import IEANTN.Nodes.Buthe.v1.Conclusions
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions

/-!
# From a bound on `Eθ` to one on `Eπ`, and the headline estimate

The paper's Theorem 3, Corollary 23 and Corollary 26. Lemma 12, the analytic heart, is proved in
`Integral.lean`.

The conversion is partial summation: `π(x) - Li(x)` is an integral of `(θ(t) - t)/(t log² t)` plus
boundary terms, so an admissible bound for `Eθ` integrates to one for `Eπ`.

## Theorem 3 needs a second threshold, and an earlier draft of this file got that wrong

The conclusion is **not** an admissible bound from `x₀` onwards. The paper's (def-x1) introduces

`x₁ ≥ max{x₀, exp((1 + C/(2√R))²)}`

and concludes for `x ≥ x₁` only. An earlier version of this file stated the conclusion at `x₀`,
which claims strictly more than the paper proves. The same draft replaced the paper's explicit
`A_π = (1 + μ_asymp(x₀, x₁)) A_θ` with `∃ Aπ`, which throws away the constant the corollaries need.
Both are recorded because the file typechecked in that state: a statement can be wrong in shape and
still compile.

## Where the two kinds of input enter

`Buthe.v1.theorem_2_li_minus_pi` supplies the mid-range, below `10¹⁹`, where the asymptotic bound
is not yet the best thing available.

`FKS2Numerics.v1.table6_row2_floor` supplies the small range `[e, e⁶]`, where the claim is a finite
check rather than analysis. **Upstream carries that as a `sorry`; here it is a hypothesis**, which
is the whole reason the numerical content was split into its own node.
-/

namespace FKS2Sol

open Real IEANTN

/-- The correction `μ_asymp(x₀, x₁)` of the paper's (mu_asymp_def).

The first summand is the boundary term at `x₀`, normalised; the second is what the integral of
Lemma 12 contributes, and it is where the Dawson function reaches the final constant. -/
noncomputable def muAsymp (Aθ B C R x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * log x₀) *
      |(primeCounting x₀ - Li x₀) / (x₀ / log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|
    + 2 * dawson (sqrt (log x₁) - C / (2 * sqrt R)) / sqrt (log x₁)

/-- **The boundary estimate.** The `x₀` boundary term, normalised, is bounded by the first
summand of `μ_asymp` times the admissible bound at `x`.

After cancelling the constant `|…|`, which appears on both sides, this reduces to

`log x / (x · ε_θ(x)) ≤ log x₁ / (x₁ · ε_θ(x₁))`,

and `log x / (x · ε_θ(x)) = (R^B / Aθ) · g(1, 1-B, C/√R, x)` is exactly the function `Growth.lean`'s
Corollary 11 shows to be decreasing. The `B ≥ 1 + C²/(16R)` hypothesis is there for this and
nothing else.

One wrinkle, already recorded as an erratum: `admissibleBound_strictAntiOn` needs that inequality
*strict*, while the paper's Theorem 3 states `≥`. At equality Lemma 10(b) applies instead, and its
threshold `exp((C/(4√R))²)` is below `x₁`, so the boundary case is covered — but by a different
lemma, which is why this is not a one-line appeal to Corollary 11. -/
theorem boundary_le {Aθ B C R x₀ x₁ x : ℝ} (hR : 0 < R)
    (hB : max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B) (hx₀ : 2 ≤ x₀)
    (hx₁ : max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)) ≤ x₁) (hx : x₁ ≤ x) (hA : 0 < Aθ) :
    (log x / x) * |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀|
      ≤ ((x₀ * log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * log x₀)
          * |(primeCounting x₀ - Li x₀) / (x₀ / log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|)
        * admissibleBound Aθ B C R x := by
  sorry

/-- **The integral estimate.** Lemma 12's bound, normalised, is at most the second summand of
`μ_asymp` times the admissible bound at `x`.

Dividing Lemma 12's conclusion by `x / log x` and then by `ε_θ(x) = Aθ R^{-B}(log x)^B e^{…}`, the
`Aθ`, `R^{-B}` and exponential factors all cancel and what is left is

`2 · mFactor · (log x)^{1-B} · D₊(√(log x) − C/(2√R))`.

For `B ≥ 3/2` the exponent `(2B-3)/2` is nonnegative, so `mFactor = (log x)^{(2B-3)/2}`, and
`(2B-3)/2 + 1 - B = -1/2`. The whole thing collapses to

`2 · D₊(√(log x) − C/(2√R)) / √(log x)`,

which `Dawson.dawson_shift_div_antitoneOn` bounds by its value at `x₁`. That is the second summand
of `μ_asymp`, and the `B ≥ 3/2` hypothesis exists exactly to make `mFactor` resolve this way. -/
theorem integral_term_le {Aθ B C R x₀ x₁ x : ℝ} (hR : 0 < R)
    (hB : max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B) (hx₀ : 2 ≤ x₀)
    (hC : C / (2 * sqrt R) ≤ sqrt (log x₀)) (hCpos : 0 ≤ C)
    (hx₁ : max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)) ≤ x₁) (hx : x₁ ≤ x)
    (h : HasClassicalBound Eθ Aθ B C R x₀) :
    (log x / x) * |∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)|
      ≤ (2 * dawson (sqrt (log x₁) - C / (2 * sqrt R)) / sqrt (log x₁))
        * admissibleBound Aθ B C R x := by
  sorry

/-- **Theorem 3**, the general `θ → π` conversion, stated as the paper does.

Three things are load-bearing and easy to lose:

* the conclusion starts at `x₁`, not `x₀` — see the module docstring;
* `A_π` is explicit, `(1 + μ_asymp(x₀, x₁)) A_θ`;
* `B ≥ max(3/2, 1 + C²/(16R))` is used twice, once per estimate above.

`hC` is the hypothesis `Integral.lean` documents as missing from the paper's Lemma 12. It is
implied by the `x₁` threshold but not by anything stated about `x₀`, and Lemma 12 is applied on
`[x₀, x]`, so it has to be assumed here too.

Given the two estimates, the rest is `Epi_le` plus the observation that `admissibleBound` is linear
in `A`. -/
theorem classicalBound_pi_of_theta
    {Aθ B C R x₀ x₁ : ℝ} (hR : 0 < R) (hB : max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B)
    (hx₀ : 2 ≤ x₀) (hA : 0 < Aθ) (hCpos : 0 ≤ C)
    (hC : C / (2 * sqrt R) ≤ sqrt (log x₀))
    (hx₁ : max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)) ≤ x₁)
    (h : HasClassicalBound Eθ Aθ B C R x₀) :
    HasClassicalBound Eπ ((1 + muAsymp Aθ B C R x₀ x₁) * Aθ) B C R x₁ := by
  intro x hx
  have hx₀x₁ : x₀ ≤ x₁ := le_trans (le_max_left _ _) hx₁
  have hx₀x : x₀ ≤ x := le_trans hx₀x₁ hx
  have hdecomp := Epi_le hx₀ hx₀x
  have hθ : Eθ x ≤ admissibleBound Aθ B C R x := h x hx₀x
  have hbdry := boundary_le hR hB hx₀ hx₁ hx hA
  have hint := integral_term_le hR hB hx₀ hC hCpos hx₁ hx h
  have hlin : admissibleBound ((1 + muAsymp Aθ B C R x₀ x₁) * Aθ) B C R x
      = admissibleBound Aθ B C R x
        + muAsymp Aθ B C R x₀ x₁ * admissibleBound Aθ B C R x := by
    unfold admissibleBound; ring
  rw [hlin]
  unfold muAsymp
  have hspread : (((x₀ * log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * log x₀)
        * |(primeCounting x₀ - Li x₀) / (x₀ / log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|)
      + 2 * dawson (sqrt (log x₁) - C / (2 * sqrt R)) / sqrt (log x₁))
        * admissibleBound Aθ B C R x
      = ((x₀ * log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * log x₀)
          * |(primeCounting x₀ - Li x₀) / (x₀ / log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|)
          * admissibleBound Aθ B C R x
        + (2 * dawson (sqrt (log x₁) - C / (2 * sqrt R)) / sqrt (log x₁))
          * admissibleBound Aθ B C R x := by ring
  rw [hspread]
  linarith

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
