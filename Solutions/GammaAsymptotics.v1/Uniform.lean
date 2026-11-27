/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Strip
import Mathlib.Analysis.Complex.RealDeriv

/-!
# A height-uniform digamma bound

The strip estimate from `GammaAsymptotics.v2` implies that, for each fixed `w`,
`digamma (w + n) - log (w + n)` tends to zero. The digamma recurrence expresses the error at
`w` as a telescoping series of logarithmic increments. A mean-value estimate bounds each
increment by `1 / ‖w + n‖²`, and a reciprocal telescoping comparison sums these bounds to
`4 / ‖w‖`, independently of the imaginary part.
-/

namespace GammaSolution

open Complex Filter Set

/-- Moving right cannot decrease the norm in the closed right half-plane. -/
theorem norm_le_norm_add_ofReal {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖w‖ ≤ ‖w + (t : ℂ)‖ := by
  have hsq : ‖w + (t : ℂ)‖ ^ 2 = ‖w‖ ^ 2 + 2 * w.re * t + t ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, ofReal_re, ofReal_im]
    ring
  nlinarith [norm_nonneg w, norm_nonneg (w + (t : ℂ)), mul_nonneg hw ht, sq_nonneg t]

/-- The error in a unit logarithmic increment is quadratic in the reciprocal norm.
The entire segment stays in the right half-plane, so there is no branch-cut identity to assume. -/
theorem norm_log_increment_sub_inv_le {w : ℂ} (hw : 1 ≤ w.re) :
    ‖Complex.log (w + 1) - Complex.log w - w⁻¹‖ ≤ 1 / ‖w‖ ^ 2 := by
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by linarith : 0 < w.re) (re_le_norm w)
  have hwne : w ≠ 0 := norm_pos_iff.mp hwpos
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ Complex.log (w + (t : ℂ)) - (t : ℂ) * w⁻¹)
        ((w + (t : ℂ))⁻¹ - w⁻¹) t := by
    have hslit : w + (t : ℂ) ∈ slitPlane := by
      apply mem_slitPlane_iff.mpr
      left
      simp only [add_re, ofReal_re]
      linarith [ht.1]
    simpa only [one_mul] using!
      (((Complex.hasDerivAt_log hslit).comp_const_add w (t : ℂ)).sub
        ((hasDerivAt_id (t : ℂ)).mul_const w⁻¹)).comp_ofReal
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖(w + (t : ℂ))⁻¹ - w⁻¹‖ ≤ 1 / ‖w‖ ^ 2 := by
    have hnorm := norm_le_norm_add_ofReal (by linarith : 0 ≤ w.re) ht.1
    have hpos : 0 < ‖w + (t : ℂ)‖ := hwpos.trans_le hnorm
    have hne : w + (t : ℂ) ≠ 0 := norm_pos_iff.mp hpos
    have heq : (w + (t : ℂ))⁻¹ - w⁻¹ = -(t : ℂ) / ((w + (t : ℂ)) * w) := by
      field_simp [hwne, hne]
      ring
    rw [heq, norm_div, norm_neg, norm_real, Real.norm_of_nonneg ht.1, norm_mul, pow_two]
    exact div_le_div₀ (by positivity) ht.2.le (by positivity)
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg w))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht ↦ (hderiv t ht).hasDerivWithinAt) hbound
  simpa only [ofReal_one, ofReal_zero, one_mul, zero_mul, add_zero, sub_zero,
    sub_right_comm] using h

/-- In a fixed horizontal strip, the error tends to zero along positive integer translates.
The strip constant may depend on `w`; it will disappear when the recurrence is telescoped. -/
theorem tendsto_digamma_sub_log_add_nat {w : ℂ} (hw : 1 ≤ w.re) :
    Tendsto (fun n : ℕ ↦ Complex.digamma (w + n) - Complex.log (w + n)) atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := digamma_sub_log_strip |w.im|
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnorm : Tendsto (fun n : ℕ ↦ ‖w + (n : ℂ)‖) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_atTop_add_const_right _ w.re hnat)
    intro n
    simpa only [add_re, natCast_re, add_comm] using re_le_norm (w + (n : ℂ))
  apply squeeze_zero_norm (fun n : ℕ ↦ hC (w + n) ?_ ?_)
  · simpa [div_eq_mul_inv] using hnorm.inv_tendsto_atTop.const_mul C
  · simp only [add_re, natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · simp only [add_im, natCast_im, add_zero, le_refl]

/-- A reciprocal-square bound with a height-independent telescoping majorant. -/
theorem inv_norm_add_nat_sq_le {w : ℂ} (hw : 1 ≤ w.re) (n : ℕ) :
    1 / ‖w + (n : ℂ)‖ ^ 2 ≤
      2 * (2 * (((n : ℝ) + ‖w‖) * ((n : ℝ) + ‖w‖ + 1))⁻¹) := by
  have hr : 1 ≤ ‖w‖ := hw.trans (re_le_norm w)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnorm : ‖w‖ ≤ ‖w + (n : ℂ)‖ := by
    simpa only [ofReal_natCast] using norm_le_norm_add_ofReal (by linarith) hn
  have hpos : 0 < ‖w + (n : ℂ)‖ := by linarith
  have hsq : ‖w + (n : ℂ)‖ ^ 2 = ‖w‖ ^ 2 + 2 * w.re * n + (n : ℝ) ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, natCast_re, natCast_im]
    ring
  have hgeom : ((n : ℝ) + ‖w‖) ^ 2 ≤ 2 * ‖w + (n : ℂ)‖ ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - ‖w‖), mul_nonneg (by linarith : 0 ≤ w.re) hn]
  have hprod : ((n : ℝ) + ‖w‖) * ((n : ℝ) + ‖w‖ + 1) ≤
      4 * ‖w + (n : ℂ)‖ ^ 2 := by
    nlinarith
  calc
    1 / ‖w + (n : ℂ)‖ ^ 2 ≤
        4 / (((n : ℝ) + ‖w‖) * ((n : ℝ) + ‖w‖ + 1)) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hpos) (by positivity)]
      simpa only [one_mul] using hprod
    _ = _ := by ring

/-- The uniform half-plane estimate, with the explicit (non-optimal) constant `4`. -/
theorem norm_digamma_sub_log_le {w : ℂ} (hw : 1 ≤ w.re) :
    ‖Complex.digamma w - Complex.log w‖ ≤ 4 / ‖w‖ := by
  let f : ℕ → ℂ := fun n ↦ Complex.digamma (w + n) - Complex.log (w + n)
  have hshift (n : ℕ) : 1 ≤ (w + (n : ℂ)).re := by
    simp only [add_re, natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hstep (n : ℕ) :
      ‖f n - f (n + 1)‖ ≤
        2 * (2 * (((n : ℝ) + ‖w‖) * ((n : ℝ) + ‖w‖ + 1))⁻¹) := by
    have hpoles : ∀ m : ℕ, w + (n : ℂ) ≠ -(m : ℂ) :=
      ne_neg_natCast_of_mem (mem_rightHalfPlane_iff.mpr (by linarith [hshift n]))
    have heq : f n - f (n + 1) =
        Complex.log ((w + n) + 1) - Complex.log (w + n) - (w + n)⁻¹ := by
      dsimp only [f]
      rw [show w + ((n + 1 : ℕ) : ℂ) = (w + n) + 1 by push_cast; ring,
        digamma_apply_add_one _ hpoles]
      ring
    rw [heq]
    exact (norm_log_increment_sub_inv_le (hshift n)).trans (inv_norm_add_nat_sq_le hw n)
  have hmajor := hasSum_comparison (hw.trans (re_le_norm w)) 2
  have hsum : Summable (fun n ↦ f n - f (n + 1)) :=
    Summable.of_norm_bounded hmajor.summable hstep
  have htel : HasSum (fun n ↦ f n - f (n + 1)) (Complex.digamma w - Complex.log w) := by
    simpa only [f, Nat.cast_zero, add_zero] using
      hasSum_sub_succ hsum (tendsto_digamma_sub_log_add_nat hw)
  have hbound := htel.norm_le_of_bounded hmajor hstep
  convert hbound using 1
  ring

end GammaSolution
