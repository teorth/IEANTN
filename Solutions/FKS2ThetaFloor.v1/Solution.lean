/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import IEANTN.Nodes.FKS2ThetaFloor.v1.Conclusions

/-!
# Solution: `FKS2ThetaFloor.v1`

The argument is the one recorded for this claim in `FKS2Numerics.v1`, from Fiori, Kadiri and
Swidinsky.

Set `u = sqrt (log x / R)` with `R = 5.5666305`. Then
`admissibleBound 121.0961 (3 / 2) 2 R x = 121.0961 * u ^ 3 * exp (-2 * u)`.
The map `g u = u ^ 3 * exp (-2 * u)` increases on `[0, 3 / 2]` and decreases on `[3 / 2, ∞)`.
For `x` in `[2, exp 30]`, `u` runs through an interval containing `3 / 2`, so the minimum of `g`
is the smaller endpoint value. Both endpoints clear `1` using Mathlib's bounds on `log 2` and
`exp (-1)`; the paper's displayed minimum of about `2.6271` is not an input.
-/

open Real Set

namespace FKS2ThetaFloor.v1.Dev

private noncomputable def g (u : ℝ) : ℝ := u ^ 3 * exp (-2 * u)

private lemma hasDerivAt_g (u : ℝ) :
    HasDerivAt g (u ^ 2 * exp (-2 * u) * (3 - 2 * u)) u := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 3) ((3 : ℝ) * u ^ 2) u := by
    simpa using hasDerivAt_pow 3 u
  have hlin : HasDerivAt (fun t : ℝ => -2 * t) (-2) u := by
    simpa using (hasDerivAt_id u).const_mul (-2)
  have hexp : HasDerivAt (fun t : ℝ => exp (-2 * t)) (exp (-2 * u) * -2) u :=
    (Real.hasDerivAt_exp (-2 * u)).comp u hlin
  have hmul := hpow.mul hexp
  rw [show (3 : ℝ) * u ^ 2 * exp (-2 * u) + u ^ 3 * (exp (-2 * u) * -2) =
      u ^ 2 * exp (-2 * u) * (3 - 2 * u) by ring] at hmul
  have hg : g = (fun t : ℝ => t ^ 3) * fun t => exp (-2 * t) := by
    funext t
    simp [g, Pi.mul_apply]
  simpa [hg] using hmul

private lemma continuous_g : Continuous g := by
  unfold g
  fun_prop

private lemma deriv_g (u : ℝ) : deriv g u = u ^ 2 * exp (-2 * u) * (3 - 2 * u) :=
  (hasDerivAt_g u).deriv

private lemma g_mono : MonotoneOn g (Icc 0 (3 / 2)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) continuous_g.continuousOn
    (fun t _ => (hasDerivAt_g t).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_g]
  have : 0 < 3 - 2 * x := by linarith [hx.2]
  positivity

private lemma g_anti : AntitoneOn g (Ici (3 / 2)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici _) continuous_g.continuousOn
    (fun t _ => (hasDerivAt_g t).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [deriv_g]
  have hx32 : 3 / 2 < x := hx
  have hneg : 3 - 2 * x < 0 := by linarith
  have hnn : 0 ≤ x ^ 2 * exp (-2 * x) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hnn hneg.le

private lemma bound_eq {x : ℝ} (hx : 1 ≤ x) :
    IEANTN.admissibleBound 121.0961 (3 / 2) 2 5.5666305 x =
      121.0961 * g (sqrt (log x / 5.5666305)) := by
  have hy : 0 ≤ log x / 5.5666305 :=
    div_nonneg (log_nonneg hx) (by norm_num)
  have hpow : (log x / 5.5666305) ^ ((3 : ℝ) / 2) =
      (sqrt (log x / 5.5666305)) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  have hexp : exp (-2 * (log x / 5.5666305) ^ ((1 : ℝ) / 2)) =
      exp (-2 * sqrt (log x / 5.5666305)) := by
    rw [Real.sqrt_eq_rpow]
  unfold IEANTN.admissibleBound g
  rw [hpow, hexp, mul_assoc]

private lemma u_two_lower : (0.35 : ℝ) ≤ sqrt (log 2 / 5.5666305) := by
  have hR : (0 : ℝ) < 5.5666305 := by norm_num
  rw [le_sqrt (by norm_num) (div_nonneg (log_nonneg (by norm_num)) hR.le), le_div_iff₀ hR]
  exact ((by norm_num : (0.35 : ℝ) ^ 2 * 5.5666305 < 0.6931471803).trans log_two_gt_d9).le

private lemma u_two_upper : sqrt (log 2 / 5.5666305) ≤ 3 / 2 := by
  rw [sqrt_le_left (by norm_num), div_le_iff₀ (by norm_num)]
  exact log_two_lt_d9.le.trans (by norm_num)

private lemma u_exp_lower : 3 / 2 ≤ sqrt (30 / 5.5666305) := by
  rw [le_sqrt (by norm_num) (div_nonneg (by norm_num) (by norm_num)), le_div_iff₀ (by norm_num)]
  norm_num

private lemma u_exp_upper : sqrt (30 / 5.5666305) ≤ 2.34 := by
  rw [sqrt_le_left (by norm_num), div_le_iff₀ (by norm_num)]
  norm_num

private lemma one_le_A_g_035 : 1 ≤ 121.0961 * g 0.35 := by
  have hbase : (1 : ℝ) ≤ 121.0961 * ((0.35 : ℝ) ^ 3 * 0.36787944116) := by
    norm_num
  have hpow : (0.35 : ℝ) ^ 3 * 0.36787944116 ≤ (0.35 : ℝ) ^ 3 * exp (-1) :=
    mul_le_mul_of_nonneg_left exp_neg_one_gt_d9.le (by positivity)
  have hg : (0.35 : ℝ) ^ 3 * exp (-1) ≤ g 0.35 := by
    unfold g
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by norm_num)) (by positivity)
  have hmul : 121.0961 * ((0.35 : ℝ) ^ 3 * 0.36787944116) ≤ 121.0961 * g 0.35 :=
    mul_le_mul_of_nonneg_left (hpow.trans hg) (by norm_num)
  exact hbase.trans hmul

private lemma one_le_A_g_234 : 1 ≤ 121.0961 * g 2.34 := by
  have hbase : (1 : ℝ) ≤ 121.0961 * ((2.34 : ℝ) ^ 3 * 0.36787944116 ^ 5) := by
    norm_num
  have hfifth : 0.36787944116 ^ 5 ≤ exp (-1) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) exp_neg_one_gt_d9.le _
  have hexp : exp (-1) ^ 5 = exp (-5) := by
    rw [← exp_nat_mul]
    norm_num
  have hpow : (2.34 : ℝ) ^ 3 * 0.36787944116 ^ 5 ≤ (2.34 : ℝ) ^ 3 * exp (-5) :=
    mul_le_mul_of_nonneg_left (hfifth.trans_eq hexp) (by positivity)
  have hg : (2.34 : ℝ) ^ 3 * exp (-5) ≤ g 2.34 := by
    unfold g
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by norm_num)) (by positivity)
  have hmul : 121.0961 * ((2.34 : ℝ) ^ 3 * 0.36787944116 ^ 5) ≤ 121.0961 * g 2.34 :=
    mul_le_mul_of_nonneg_left (hpow.trans hg) (by norm_num)
  exact hbase.trans hmul

private lemma one_le_endpoints :
    1 ≤ 121.0961 * g (sqrt (log 2 / 5.5666305)) ∧
      1 ≤ 121.0961 * g (sqrt (30 / 5.5666305)) := by
  refine ⟨?_, ?_⟩
  · have hmem₀ : (0.35 : ℝ) ∈ Icc 0 (3 / 2) := by constructor <;> norm_num
    have hmem : sqrt (log 2 / 5.5666305) ∈ Icc 0 (3 / 2) :=
      ⟨sqrt_nonneg _, u_two_upper⟩
    have hg : g 0.35 ≤ g (sqrt (log 2 / 5.5666305)) := g_mono hmem₀ hmem u_two_lower
    exact one_le_A_g_035.trans (mul_le_mul_of_nonneg_left hg (by norm_num))
  · have hmem₁ : (2.34 : ℝ) ∈ Ici (3 / 2) := by
      rw [mem_Ici]
      norm_num
    have hmem : sqrt (30 / 5.5666305) ∈ Ici (3 / 2) := mem_Ici.mpr u_exp_lower
    have hle : sqrt (30 / 5.5666305) ≤ 2.34 := u_exp_upper
    have hg : g 2.34 ≤ g (sqrt (30 / 5.5666305)) := g_anti hmem hmem₁ hle
    exact one_le_A_g_234.trans (mul_le_mul_of_nonneg_left hg (by norm_num))

theorem theta_asymp_ge_one_below_e30 :
    FKS2ThetaFloor.v1.theta_asymp_ge_one_below_e30 := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := hx.1.trans' (by norm_num)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hmargin : IEANTN.margin 0 = 1 := by simp [IEANTN.margin]
  rw [hmargin, one_mul, bound_eq hx1]
  have hlog₁ : log 2 ≤ log x := log_le_log (by norm_num) hx.1
  have hlog₂ : log x ≤ 30 := by
    rw [← log_exp 30]
    exact log_le_log hxpos hx.2
  have hdiv₁ : log 2 / 5.5666305 ≤ log x / 5.5666305 := by
    gcongr
  have hdiv₂ : log x / 5.5666305 ≤ 30 / 5.5666305 := by
    gcongr
  have hu₁ : sqrt (log 2 / 5.5666305) ≤ sqrt (log x / 5.5666305) := sqrt_le_sqrt hdiv₁
  have hu₂ : sqrt (log x / 5.5666305) ≤ sqrt (30 / 5.5666305) := sqrt_le_sqrt hdiv₂
  have ha : sqrt (log 2 / 5.5666305) ≤ 3 / 2 := u_two_upper
  have hb : 3 / 2 ≤ sqrt (30 / 5.5666305) := u_exp_lower
  set a : ℝ := sqrt (log 2 / 5.5666305)
  set b : ℝ := sqrt (30 / 5.5666305)
  set u : ℝ := sqrt (log x / 5.5666305)
  have hgu : min (g a) (g b) ≤ g u := by
    by_cases hu : u ≤ 3 / 2
    · have hmema : a ∈ Icc 0 (3 / 2) := ⟨sqrt_nonneg _, ha⟩
      have hmemu : u ∈ Icc 0 (3 / 2) := ⟨sqrt_nonneg _, hu⟩
      exact (min_le_left _ _).trans (g_mono hmema hmemu hu₁)
    · have hu' : 3 / 2 ≤ u := le_of_not_ge hu
      have hmemu : u ∈ Ici (3 / 2) := mem_Ici.mpr hu'
      have hmemb : b ∈ Ici (3 / 2) := mem_Ici.mpr hb
      exact (min_le_right _ _).trans (g_anti hmemu hmemb hu₂)
  have hends := one_le_endpoints
  have hmin : 1 ≤ 121.0961 * min (g a) (g b) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 121.0961)]
    exact le_min hends.1 hends.2
  exact hmin.trans (mul_le_mul_of_nonneg_left hgu (by norm_num))

end FKS2ThetaFloor.v1.Dev

theorem FKS2ThetaFloor.v1.challenge_theta_asymp_ge_one_below_e30 :
    FKS2ThetaFloor.v1.theta_asymp_ge_one_below_e30 :=
  FKS2ThetaFloor.v1.Dev.theta_asymp_ge_one_below_e30
