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
open FKS2.v1 (muAsymp dawson)

/-- `log y / (y · ε_θ(y)) = (R^B/Aθ) · g(1, 1−B, C/√R, y)`, the function Corollary 11 governs.

This identity is the whole reason `Growth.lean` exists in the shape it does. -/
theorem log_div_admissibleBound {Aθ B C R : ℝ} (hR : 0 < R) (hA : 0 < Aθ) {y : ℝ} (hy : 1 < y) :
    log y / (y * admissibleBound Aθ B C R y) = (R ^ B / Aθ) * g 1 (1 - B) (C / sqrt R) y := by
  have hly : 0 < log y := log_pos hy
  have hypos : (0 : ℝ) < y := by linarith
  have hRB : (0 : ℝ) < R ^ B := rpow_pos_of_pos hR B
  have hLB : (0 : ℝ) < (log y) ^ B := rpow_pos_of_pos hly B
  have hpow : log y = (log y) ^ (1 - B) * (log y) ^ B := by
    rw [← rpow_add hly, show (1 - B) + B = (1 : ℝ) by ring, rpow_one]
  have hyinv : y ^ (-(1 : ℝ)) = y⁻¹ := by rw [rpow_neg hypos.le, rpow_one]
  have hEeq : exp (-(C / sqrt R) * sqrt (log y)) = (exp (C / sqrt R * sqrt (log y)))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hEp : (0 : ℝ) < exp (C / sqrt R * sqrt (log y)) := exp_pos _
  have key : ∀ L LB L1B E : ℝ, LB ≠ 0 → E ≠ 0 → L = L1B * LB →
      L / (y * (Aθ * (R ^ B)⁻¹ * (LB * E⁻¹))) = R ^ B / Aθ * (y⁻¹ * L1B * E) := by
    intro L LB L1B E hLB' hE' hrel
    rw [hrel]
    field_simp
  rw [admissibleBound_eq_g_mul hR hy, rpow_neg hR.le, hEeq]
  unfold g
  rw [hyinv]
  exact key _ _ _ _ hLB.ne' hEp.ne' hpow

theorem boundary_le {Aθ B C R x₀ x₁ x : ℝ} (hR : 0 < R)
    (hB : max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B) (hx₀ : 2 ≤ x₀) (hCpos : 0 < C)
    (hx₁ : max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)) ≤ x₁) (hx : x₁ ≤ x) (hA : 0 < Aθ) :
    (log x / x) * |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀|
      ≤ ((x₀ * log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * log x₀)
          * |(primeCounting x₀ - Li x₀) / (x₀ / log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|)
        * admissibleBound Aθ B C R x := by
  have hx₀1 : (1 : ℝ) < x₀ := by linarith
  have hx₀x₁ : x₀ ≤ x₁ := le_trans (le_max_left _ _) hx₁
  have hx₁1 : (1 : ℝ) < x₁ := lt_of_lt_of_le hx₀1 hx₀x₁
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hx₁1 hx
  have hx₀pos : (0 : ℝ) < x₀ := by linarith
  have hx₁pos : (0 : ℝ) < x₁ := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hl₀ : 0 < log x₀ := log_pos hx₀1
  have hl₁ : 0 < log x₁ := log_pos hx₁1
  have hlx : 0 < log x := log_pos hx1
  have hsr : (0 : ℝ) < sqrt R := sqrt_pos.mpr hR
  have hc : (0 : ℝ) < C / sqrt R := by positivity
  have hKrel : |(primeCounting x₀ - Li x₀) / (x₀ / log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|
      = (log x₀ / x₀) * |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀| := by
    rw [← abs_of_pos (show (0 : ℝ) < log x₀ / x₀ by positivity), ← abs_mul]
    congr 1
    field_simp
  have hbb : 1 - B ≤ -(C / sqrt R) ^ 2 / (16 * 1) := by
    have hsq : (C / sqrt R) ^ 2 = C ^ 2 / R := by rw [div_pow, sq_sqrt hR.le]
    have hle : 1 + C ^ 2 / (16 * R) ≤ B := le_trans (le_max_right _ _) hB
    have h16 : C ^ 2 / R / (16 * 1) = C ^ 2 / (16 * R) := by field_simp
    rw [hsq, neg_div, h16]
    linarith
  set X := exp ((C / sqrt R / (4 * 1)) ^ 2) with hXdef
  have hX1 : 1 < X := by
    rw [hXdef, show (1 : ℝ) = exp 0 from Real.exp_zero.symm]
    exact exp_lt_exp.mpr (by positivity)
  have hXlt : X < x₁ := by
    refine lt_of_lt_of_le ?_ (le_trans (le_max_right _ _) hx₁)
    have hd2 : C / (2 * sqrt R) = C / sqrt R / 2 := by field_simp
    rw [hXdef, hd2]
    exact exp_lt_exp.mpr (by nlinarith [hc])
  have hanti := g_strictAntiOn_of_le (a := 1) (b := 1 - B) (c := C / sqrt R)
    one_pos hc hbb hX1 (le_refl X)
  have hgle : g 1 (1 - B) (C / sqrt R) x ≤ g 1 (1 - B) (C / sqrt R) x₁ := by
    rcases eq_or_lt_of_le hx with heq | hlt
    · rw [heq]
    · exact (hanti (Set.mem_Ioi.mpr hXlt) (Set.mem_Ioi.mpr (lt_trans hXlt hlt)) hlt).le
  have hε₁ : (0 : ℝ) < admissibleBound Aθ B C R x₁ := by
    rw [admissibleBound_eq_g_mul hR hx₁1]
    exact mul_pos (mul_pos hA (rpow_pos_of_pos hR _))
      (mul_pos (rpow_pos_of_pos hl₁ _) (exp_pos _))
  have hεx : (0 : ℝ) < admissibleBound Aθ B C R x := by
    rw [admissibleBound_eq_g_mul hR hx1]
    exact mul_pos (mul_pos hA (rpow_pos_of_pos hR _))
      (mul_pos (rpow_pos_of_pos hlx _) (exp_pos _))
  have hratio : log x / (x * admissibleBound Aθ B C R x)
      ≤ log x₁ / (x₁ * admissibleBound Aθ B C R x₁) := by
    rw [log_div_admissibleBound hR hA hx1, log_div_admissibleBound hR hA hx₁1]
    exact mul_le_mul_of_nonneg_left hgle (by positivity)
  rw [hKrel]
  have hK0 : (0 : ℝ) ≤ |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀| :=
    abs_nonneg _
  have hfinal : log x / x ≤ (log x₁ / (admissibleBound Aθ B C R x₁ * x₁))
      * admissibleBound Aθ B C R x := by
    calc log x / x
        = log x / (x * admissibleBound Aθ B C R x) * admissibleBound Aθ B C R x := by
          field_simp
      _ ≤ log x₁ / (x₁ * admissibleBound Aθ B C R x₁) * admissibleBound Aθ B C R x :=
          mul_le_mul_of_nonneg_right hratio hεx.le
      _ = (log x₁ / (admissibleBound Aθ B C R x₁ * x₁)) * admissibleBound Aθ B C R x := by
          rw [mul_comm x₁ (admissibleBound Aθ B C R x₁)]
  have hexpand : ((x₀ * log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * log x₀)
      * ((log x₀ / x₀) * |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀|))
      * admissibleBound Aθ B C R x
      = ((log x₁ / (admissibleBound Aθ B C R x₁ * x₁)) * admissibleBound Aθ B C R x)
        * |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀| := by
    field_simp
  rw [hexpand]
  exact mul_le_mul_of_nonneg_right hfinal hK0

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
  have hx₀1 : (1 : ℝ) < x₀ := by linarith
  have hx₀x₁ : x₀ ≤ x₁ := le_trans (le_max_left _ _) hx₁
  have hx₀x : x₀ ≤ x := le_trans hx₀x₁ hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hx₀1 hx₀x
  have hxpos : (0 : ℝ) < x := by linarith
  have hL : 0 < log x := log_pos hx1
  have hL₁ : 0 < log x₁ := log_pos (lt_of_lt_of_le hx₀1 hx₀x₁)
  have hsr : (0 : ℝ) < sqrt R := sqrt_pos.mpr hR
  have hsne : sqrt (log x) ≠ 0 := (sqrt_pos.mpr hL).ne'
  have hRne : (R : ℝ) ^ B ≠ 0 := (rpow_pos_of_pos hR B).ne'
  have hA : 0 ≤ Aθ := by
    have h0 := h x₀ (le_refl x₀)
    have hE : 0 ≤ Eθ x₀ := by unfold Eθ; positivity
    have hq : 0 < log x₀ / R := div_pos (log_pos hx₀1) hR
    have hpos : 0 < (log x₀ / R) ^ B * exp (-C * (log x₀ / R) ^ ((1 : ℝ) / 2)) :=
      mul_pos (rpow_pos_of_pos hq B) (exp_pos _)
    unfold admissibleBound at h0
    nlinarith [h0, hE, hpos]
  have hc0 : (0 : ℝ) ≤ C / (2 * sqrt R) := div_nonneg hCpos (by positivity)
  have habs : |∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)|
      ≤ ∫ t in x₀..x, |Chebyshev.theta t - t| / (t * (log t) ^ 2) := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hx₀x) (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx₀x] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hx₀1 ht.1
    have hp : (0 : ℝ) < t * (log t) ^ 2 := by have := log_pos ht1; positivity
    rw [abs_div, abs_of_pos hp]
  have h12 := integral_theta_bound hR hx₀1 hC h hx₀x
  have hmB : (0 : ℝ) ≤ (2 * B - 3) / 2 := by
    have : (3 : ℝ) / 2 ≤ B := le_trans (le_max_left _ _) hB
    linarith
  have hmax : mFactor B x₀ x = (log x) ^ ((2 * B - 3) / 2) :=
    max_eq_right (rpow_le_rpow (log_pos hx₀1).le (log_le_log (by linarith) hx₀x) hmB)
  -- `(log x)^{(2B-3)/2} · log x · √(log x) = (log x)^B`: the whole rpow content.
  have hpow3 : (log x) ^ ((2 * B - 3) / 2) * log x * sqrt (log x) = (log x) ^ B := by
    have e1 : log x = (log x) ^ (1 : ℝ) := (rpow_one _).symm
    have e2 : sqrt (log x) = (log x) ^ ((1 : ℝ) / 2) := sqrt_eq_rpow _
    calc (log x) ^ ((2 * B - 3) / 2) * log x * sqrt (log x)
        = (log x) ^ ((2 * B - 3) / 2) * (log x) ^ (1 : ℝ) * (log x) ^ ((1 : ℝ) / 2) := by
          rw [← e1, ← e2]
      _ = (log x) ^ ((2 * B - 3) / 2 + 1 + (1 : ℝ) / 2) := by
          rw [← rpow_add hL, ← rpow_add hL]
      _ = (log x) ^ B := by congr 1; ring
  have hadm : admissibleBound Aθ B C R x
      = Aθ * (R ^ B)⁻¹ * ((log x) ^ B * exp (-C * sqrt (log x / R))) := by
    have hs : (log x / R) ^ ((1 : ℝ) / 2) = sqrt (log x / R) := (sqrt_eq_rpow _).symm
    unfold admissibleBound
    rw [hs, div_rpow hL.le hR.le]
    field_simp
  -- Pure algebra, with the transcendental parts held as variables.
  have key : ∀ D E : ℝ,
      (log x / x) * (2 * Aθ / R ^ B * x * (log x) ^ ((2 * B - 3) / 2) * E * D)
        = (2 * D / sqrt (log x)) * (Aθ * (R ^ B)⁻¹ * ((log x) ^ B * E)) := by
    intro D E
    rw [← hpow3]
    field_simp
  have hstep : (log x / x) * |∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)|
      ≤ (2 * dawson (sqrt (log x) - C / (2 * sqrt R)) / sqrt (log x))
        * admissibleBound Aθ B C R x := by
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans habs h12)
      (by positivity : (0 : ℝ) ≤ log x / x)) (le_of_eq ?_)
    rw [hmax, hadm]
    exact key _ _
  refine le_trans hstep ?_
  -- Dawson monotonicity: this is what the `x₁` threshold buys.
  have hs₁ : 1 + C / (2 * sqrt R) ≤ sqrt (log x₁) := by
    have hge : exp ((1 + C / (2 * sqrt R)) ^ 2) ≤ x₁ := le_trans (le_max_right _ _) hx₁
    have hlog : (1 + C / (2 * sqrt R)) ^ 2 ≤ log x₁ := by
      rw [← Real.log_exp ((1 + C / (2 * sqrt R)) ^ 2)]
      exact log_le_log (exp_pos _) hge
    calc 1 + C / (2 * sqrt R) = sqrt ((1 + C / (2 * sqrt R)) ^ 2) := (sqrt_sq (by linarith)).symm
      _ ≤ sqrt (log x₁) := sqrt_le_sqrt hlog
  have hss : sqrt (log x₁) ≤ sqrt (log x) := sqrt_le_sqrt (log_le_log (by linarith) hx)
  have hdaw := dawson_shift_div_antitoneOn hc0 hs₁ hss
  have hpos : (0 : ℝ) ≤ admissibleBound Aθ B C R x := by rw [hadm]; positivity
  refine mul_le_mul_of_nonneg_right ?_ hpos
  rw [mul_div_assoc, mul_div_assoc]
  linarith [hdaw]

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
    (hx₀ : 2 ≤ x₀) (hA : 0 < Aθ) (hCpos : 0 < C)
    (hC : C / (2 * sqrt R) ≤ sqrt (log x₀))
    (hx₁ : max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)) ≤ x₁)
    (h : HasClassicalBound Eθ Aθ B C R x₀) :
    HasClassicalBound Eπ ((1 + muAsymp Aθ B C R x₀ x₁) * Aθ) B C R x₁ := by
  intro x hx
  have hx₀x₁ : x₀ ≤ x₁ := le_trans (le_max_left _ _) hx₁
  have hx₀x : x₀ ≤ x := le_trans hx₀x₁ hx
  have hdecomp := Epi_le hx₀ hx₀x
  have hθ : Eθ x ≤ admissibleBound Aθ B C R x := h x hx₀x
  have hbdry := boundary_le hR hB hx₀ hCpos hx₁ hx hA
  have hint := integral_term_le hR hB hx₀ hC hCpos.le hx₁ hx h
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

**This does not come from Theorem 3.** Theorem 3 preserves `B` and `C` and requires
`B ≥ max(3/2, 1 + C²/(16R))`. Corollary 14 supplies `B = 3/2, C = 2`; this row is `B = 1/4, C = 1`,
so Theorem 3 can neither change the parameters nor accept `B = 1/4`. The paper's Remark
`rem-pi2theta` notes the `B ≥ 3/2` restriction could be lifted but never states the generalisation.

**It does not need it either.** The route is to split the range. Against Corollary 22, the paper's
headline bound (`9.2211 (log x)^{3/2} e^{-0.84768√log x}`), the ratio in `s = √(log x)` is
`≈ 17.1 s^{5/2} e^{-0.42385 s}`: it peaks near `118.9` at `x ≈ e^34.8`, so Corollary 22 does *not*
dominate on all of `[e, ∞)` — but it does from about `x ≈ e^671` onward, and below that other means
cover the range.

`PrimeNumberTheoremAnd` does exactly this, in four pieces: Corollary 22 domination on
`[e²⁰⁰⁰⁰, ∞)`, a numerical "quarter transport" over extended Table 4 cells on `[e¹⁰, e²⁰⁰⁰⁰]`, a
Büthe assembler on `[e⁶, e¹⁰]`, and one trusted numerical floor on `[e, e⁶]` — which is precisely
`FKS2Numerics.v1.table6_row2_floor`. So what this hole needs is numerical inputs and range
bookkeeping, not new analysis.

(An earlier version of this docstring said the row followed from Theorem 3 — wrong — and a later
one said it followed from nothing the paper states, which over-corrected: the peak figure is right
but it only rules out domination on the *whole* range.) -/
theorem corollary_23
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi)
    (hfloor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_23 := by
  sorry

/-- **Corollary 26**, the paper's headline: `|π(x) - Li(x)| ≤ 0.4298 x / log x` for all `x ≥ 2`.

Two routes, and they are not the same.

`PrimeNumberTheoremAnd` derives it from Corollary 23: for `x ≥ e` the admissible bound's maximum
on `[e, ∞)` is about `0.3543 < 0.4298`, and `2 ≤ x < e` is direct because `π(x) = 1` there. That
route is valid and is the one this file would take, but it inherits Corollary 23's difficulty.

**The paper does not go that way at all.** Its proof of `cor:weak` is numerical throughout: the 25
prime intervals below `97`, then Büthe's Theorem 2 on `[97, 10¹⁹]` verifying
`(1/√x)(1.95 + 3.9/log x + 19.5/log²x) ≤ 0.4298`, then its own numerical proposition with Table 4
above `10¹⁹`. The node's recorded imports follow the paper's route, not upstream's. -/
theorem corollary_26
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi) :
    FKS2.v1.corollary_26 := by
  sorry

end FKS2Sol
