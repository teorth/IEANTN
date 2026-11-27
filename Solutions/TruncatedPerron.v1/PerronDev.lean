/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Doolan
-/
import Mathlib

/-!
# The single-term truncated Perron bound

Montgomery–Vaughan Theorem 5.2 kernel / Titchmarsh §3.12: for `c, T, y > 0`, `y ≠ 1`,
`‖perronT y c T - 1_{y>1}‖ ≤ y^c · min 1 (1/(πT|log y|))` (`TruncPerron.perron_single`).
Finite interval integrals only.

* The `1/(πT|log y|)` half: rectangle contour shifts (left with the residue at `0` for `y > 1`,
  right for `y < 1`), with the far side bounded for each width and no limits of integrals.
* The `1` half: a circular arc of radius `‖c + iT‖`, via a primitive on a disc
  (`DifferentiableOn.isExactOn_ball`).

The definitions of `HIntegral`, `VIntegral`, `RectangleIntegral` and the rectangle integral of
`1/s` are adapted from PrimeNumberTheoremAnd (`ResidueCalcOnRectangles.lean`, Apache-2.0).
-/

open Complex Real MeasureTheory intervalIntegral Set
open scoped Interval

namespace TruncPerron

noncomputable section

/-! ### Rectangle integrals (definitions follow PrimeNumberTheoremAnd) -/

def HIntegral (f : ℂ → ℂ) (x₁ x₂ y : ℝ) : ℂ := ∫ x in x₁..x₂, f (x + y * I)

def VIntegral (f : ℂ → ℂ) (x y₁ y₂ : ℝ) : ℂ := I * ∫ y in y₁..y₂, f (x + y * I)

def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

theorem rectangleIntegral_eq_zero {f : ℂ → ℂ} {z w : ℂ}
    (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    RectangleIntegral f z w = 0 := by
  simpa [RectangleIntegral, HIntegral, VIntegral] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf

/-! ### Rectangle integral of `1/s` (adapted from PrimeNumberTheoremAnd) -/

lemma inv_re_add_im' (x y : ℝ) : ((x : ℂ) + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero' {x y : ℝ} (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq {y : ℝ} (hy : y ≠ 0) :
    Continuous fun x : ℝ => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
    (fun _ => sq_add_sq_ne_zero' hy)

lemma integral_self_div_sq_add_sq {x₁ x₂ y : ℝ} (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x : ℝ} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x : ℝ} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    refine HasDerivAt.congr_deriv ((e1.log (sq_add_sq_ne_zero' hy)).div_const 2) ?_
    ring
  exact integral_eq_sub_of_hasDerivAt (fun _ _ => e2)
    ((continuous_self_div_sq_add_sq hy).intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq {x₁ x₂ y : ℝ} (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

lemma integral_const_div_self_add_im {x₁ x₂ y : ℝ} {A : ℂ} (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im']
    ring
  have e2 : IntervalIntegrable (fun x : ℝ ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x : ℝ ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero' hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self {y₁ y₂ x : ℝ} {A : ℂ} (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : (x : ℂ) + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : (y : ℂ) + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma rectangleIntegral_inv {z w : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => 1 / s) z w = 2 * I * π := by
  have key : ∀ c : ℂ, RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
    intro c
    simp only [RectangleIntegral, HIntegral, VIntegral]
    rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
    rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
    have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
    have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
    have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
    have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
    have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
    have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
    have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
    have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
    ring_nf
    simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, Real.arctan_neg, ofReal_neg,
      sub_neg_eq_add]
    rw [l1, l3, l4, l6, r1, r3, r4, r6]
    ring_nf
    simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
    ring_nf
  simpa using key 1

/-! ### The Perron integrand -/

/-- `y ^ s / s`. -/
def F (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ s / s

/-- `(y ^ s - 1) / s`, extended holomorphically to `s = 0`. -/
def G (y : ℝ) : ℂ → ℂ := dslope (fun s : ℂ => (y : ℂ) ^ s) 0

lemma differentiable_cpow_const {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ s) := fun s =>
  (differentiableAt_id).const_cpow (Or.inl (by exact_mod_cast hy.ne'))

lemma differentiable_G {y : ℝ} (hy : 0 < y) : Differentiable ℂ (G y) := by
  have := (differentiableOn_dslope (s := univ) (c := 0) (f := fun s : ℂ => (y : ℂ) ^ s)
    Filter.univ_mem).mpr (differentiable_cpow_const hy).differentiableOn
  exact fun s => (this s (mem_univ s)).differentiableAt Filter.univ_mem

lemma F_eq_G_add {y : ℝ} {s : ℂ} (hs : s ≠ 0) : F y s = G y s + 1 / s := by
  simp only [F, G, dslope_of_ne _ hs, slope_def_field, cpow_zero, sub_zero]
  field_simp
  ring

lemma ne_zero_of_im {x t : ℝ} (ht : t ≠ 0) : (x : ℂ) + t * I ≠ 0 := by
  intro h; apply ht; simpa using congr_arg im h

lemma ne_zero_of_re {x t : ℝ} (hx : x ≠ 0) : (x : ℂ) + t * I ≠ 0 := by
  intro h; apply hx; simpa using congr_arg re h

lemma continuous_inv_H {t : ℝ} (ht : t ≠ 0) :
    Continuous fun x : ℝ => 1 / ((x : ℂ) + t * I) :=
  continuous_const.div (by fun_prop) (fun _ => ne_zero_of_im ht)

lemma continuous_inv_V {x : ℝ} (hx : x ≠ 0) :
    Continuous fun t : ℝ => 1 / ((x : ℂ) + t * I) :=
  continuous_const.div (by fun_prop) (fun _ => ne_zero_of_re hx)

lemma HIntegral_split {y : ℝ} (hy : 0 < y) {a b t : ℝ} (ht : t ≠ 0) :
    HIntegral (F y) a b t = HIntegral (G y) a b t + HIntegral (fun s => 1 / s) a b t := by
  simp only [HIntegral]
  rw [← intervalIntegral.integral_add]
  · exact integral_congr fun x _ => F_eq_G_add (ne_zero_of_im ht)
  · exact ((differentiable_G hy).continuous.comp (by fun_prop)).intervalIntegrable _ _
  · exact (continuous_inv_H ht).intervalIntegrable _ _

lemma VIntegral_split {y : ℝ} (hy : 0 < y) {x a b : ℝ} (hx : x ≠ 0) :
    VIntegral (F y) x a b = VIntegral (G y) x a b + VIntegral (fun s => 1 / s) x a b := by
  simp only [VIntegral]
  rw [← mul_add, ← intervalIntegral.integral_add]
  · exact congrArg _ (integral_congr fun t _ => F_eq_G_add (ne_zero_of_re hx))
  · exact ((differentiable_G hy).continuous.comp (by fun_prop)).intervalIntegrable _ _
  · exact (continuous_inv_V hx).intervalIntegrable _ _

/-- Residue theorem for `y^s/s` on a rectangle around `0`. -/
theorem rectangleIntegral_F {y U c T : ℝ} (hy : 0 < y) (hU : 0 < U) (hc : 0 < c) (hT : 0 < T) :
    RectangleIntegral (F y) (-U - T * I) (c + T * I) = 2 * I * π := by
  have hre1 : (-(U : ℂ) - T * I).re = -U := by simp
  have him1 : (-(U : ℂ) - T * I).im = -T := by simp
  have hre2 : ((c : ℂ) + T * I).re = c := by simp
  have him2 : ((c : ℂ) + T * I).im = T := by simp
  have hG := rectangleIntegral_eq_zero (f := G y) (z := -U - T * I) (w := c + T * I)
    (differentiable_G hy).differentiableOn
  have hI := rectangleIntegral_inv (z := -U - T * I) (w := c + T * I)
    (by rw [hre1]; linarith) (by rw [him1]; linarith) (by rw [hre2]; linarith)
    (by rw [him2]; linarith)
  simp only [RectangleIntegral, hre1, him1, hre2, him2] at hG hI ⊢
  rw [HIntegral_split hy (by linarith : -T ≠ 0), HIntegral_split hy hT.ne',
    VIntegral_split hy hc.ne', VIntegral_split hy (by linarith : -U ≠ 0)]
  linear_combination hG + hI

/-- Cauchy for `y^s/s` on a rectangle in the right half-plane. -/
theorem rectangleIntegral_F_right {y U c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hcU : c ≤ U) :
    RectangleIntegral (F y) (c - T * I) (U + T * I) = 0 := by
  apply rectangleIntegral_eq_zero
  intro s hs
  have hsre : c ≤ s.re := by
    have := hs.1
    simp only [mem_preimage, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, add_re] at this
    rw [uIcc_of_le (by simpa using hcU)] at this
    simpa using this.1
  have hs0 : s ≠ 0 := by rintro rfl; simp at hsre; linarith
  exact ((differentiable_cpow_const hy s).div differentiableAt_id hs0).differentiableWithinAt

/-! ### Bounds on the sides -/

lemma norm_F {y : ℝ} (hy : 0 < y) (x t : ℝ) :
    ‖F y (x + t * I)‖ = y ^ x / ‖(x : ℂ) + t * I‖ := by
  simp [F, norm_cpow_eq_rpow_re_of_pos hy]

lemma norm_add_mul_I_ge_im (x t : ℝ) : |t| ≤ ‖(x : ℂ) + t * I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) + t * I)

lemma norm_add_mul_I_ge_re (x t : ℝ) : |x| ≤ ‖(x : ℂ) + t * I‖ := by
  simpa using Complex.abs_re_le_norm ((x : ℂ) + t * I)

lemma integral_rpow_const {y a b : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    ∫ x in a..b, y ^ x = (y ^ b - y ^ a) / Real.log y := by
  have hl : Real.log y ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact hy1 h; linarith]
  rw [integral_eq_sub_of_hasDerivAt (f := fun x => y ^ x / Real.log y)]
  · ring
  · intro x _
    have := (Real.hasStrictDerivAt_const_rpow hy x).hasDerivAt.div_const (Real.log y)
    simpa [hl] using this
  · exact (continuous_const.rpow continuous_id (fun _ => Or.inl hy.ne')).intervalIntegrable _ _

/-- Horizontal side bound. -/
lemma norm_HIntegral_le {y a b t : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hab : a ≤ b) (ht : t ≠ 0) :
    ‖HIntegral (F y) a b t‖ ≤ (y ^ b - y ^ a) / (Real.log y * |t|) := by
  have hta : 0 < |t| := abs_pos.mpr ht
  calc ‖HIntegral (F y) a b t‖ ≤ ∫ x in a..b, y ^ x / |t| := by
        apply norm_integral_le_of_norm_le hab
        · refine Filter.Eventually.of_forall fun x _ => ?_
          rw [norm_F hy]
          exact div_le_div_of_nonneg_left (by positivity) hta (norm_add_mul_I_ge_im x t)
        · exact ((continuous_const.rpow continuous_id (fun _ => Or.inl hy.ne')).div_const
            _).intervalIntegrable _ _
    _ = (y ^ b - y ^ a) / (Real.log y * |t|) := by
        rw [intervalIntegral.integral_div, integral_rpow_const hy hy1]
        ring

/-- Vertical side bound, crude. -/
lemma norm_VIntegral_le {y x T : ℝ} (hy : 0 < y) (hx : x ≠ 0) (hT : 0 ≤ T) :
    ‖VIntegral (F y) x (-T) T‖ ≤ y ^ x / |x| * (2 * T) := by
  have hxa : 0 < |x| := abs_pos.mpr hx
  simp only [VIntegral, norm_mul, norm_I, one_mul]
  have := norm_integral_le_of_norm_le_const (a := -T) (b := T) (C := y ^ x / |x|)
    (f := fun t : ℝ => F y (x + t * I)) (fun t _ => by
      rw [norm_F hy]
      exact div_le_div_of_nonneg_left (by positivity) hxa (norm_add_mul_I_ge_re x t))
  rw [show |T - -T| = 2 * T by rw [abs_of_nonneg (by linarith)]; ring] at this
  exact this

/-! ### Main theorems -/

/-- The truncated Perron integral `(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds`. -/
def perronT (y c T : ℝ) : ℂ := (1 / (2 * π * I)) * VIntegral (F y) c (-T) T

lemma perronT_sub (y c T : ℝ) (A : ℂ) :
    ‖perronT y c T - A‖ = ‖VIntegral (F y) c (-T) T - 2 * π * I * A‖ / (2 * π) := by
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero, I_ne_zero]
  rw [perronT, show (1 / (2 * π * I)) * VIntegral (F y) c (-T) T - A =
      (VIntegral (F y) c (-T) T - 2 * π * I * A) / (2 * π * I) by field_simp]
  rw [norm_div]
  congr 1
  simp [abs_of_pos pi_pos]

/-- **Truncated Perron, single term, `y > 1`.** -/
theorem perron_gt_one {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronT y c T - 1‖ ≤ y ^ c / (π * T * Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos hy
  rw [perronT_sub, mul_one]
  -- For every `U > 0`, `‖V - 2πi‖ ≤ 2 y^c/(T log y) + 2T/U`.
  have main : ∀ U : ℝ, 0 < U →
      ‖VIntegral (F y) c (-T) T - 2 * π * I‖ ≤ 2 * (y ^ c / (Real.log y * T)) + 2 * T / U := by
    intro U hU
    have hR := rectangleIntegral_F hy0 hU hc hT
    simp only [RectangleIntegral] at hR
    have hre1 : (-(U : ℂ) - T * I).re = -U := by simp
    have him1 : (-(U : ℂ) - T * I).im = -T := by simp
    have hre2 : ((c : ℂ) + T * I).re = c := by simp
    have him2 : ((c : ℂ) + T * I).im = T := by simp
    rw [hre1, him1, hre2, him2] at hR
    have hV : VIntegral (F y) c (-T) T - 2 * π * I =
        HIntegral (F y) (-U) c T - HIntegral (F y) (-U) c (-T) + VIntegral (F y) (-U) (-T) T := by
      linear_combination hR
    rw [hV]
    have h1 := norm_HIntegral_le hy0 hy.ne' (by linarith : -U ≤ c) hT.ne'
    have h2 := norm_HIntegral_le hy0 hy.ne' (by linarith : -U ≤ c) (by linarith : -T ≠ 0)
    have h3 := norm_VIntegral_le hy0 (by linarith : -U ≠ 0) hT.le
    rw [abs_neg, abs_of_pos hT] at h2
    rw [abs_of_pos hT] at h1
    rw [abs_neg, abs_of_pos hU] at h3
    have hyU : y ^ (-U) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy.le (by linarith)
    have hyU0 : 0 < y ^ (-U) := Real.rpow_pos_of_pos hy0 _
    have hlt : 0 < Real.log y * T := mul_pos hl hT
    have e1 : (y ^ c - y ^ (-U)) / (Real.log y * T) ≤ y ^ c / (Real.log y * T) :=
      div_le_div_of_nonneg_right (by linarith) hlt.le
    have e2 : y ^ (-U) / U * (2 * T) ≤ 2 * T / U := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hU]; nlinarith
    calc _ ≤ ‖HIntegral (F y) (-U) c T‖ + ‖HIntegral (F y) (-U) c (-T)‖ +
          ‖VIntegral (F y) (-U) (-T) T‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ _ := by linarith
  have key : ‖VIntegral (F y) c (-T) T - 2 * π * I‖ ≤ 2 * (y ^ c / (Real.log y * T)) := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have := main (4 * T / ε) (by positivity)
    have : 2 * T / (4 * T / ε) = ε / 2 := by field_simp; ring
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ 2 * (y ^ c / (Real.log y * T)) := key
    _ = _ := by field_simp

/-- **Truncated Perron, single term, `0 < y < 1`.** -/
theorem perron_lt_one {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronT y c T‖ ≤ y ^ c / (π * T * |Real.log y|) := by
  have hl : Real.log y < 0 := Real.log_neg hy0 hy
  have habs : |Real.log y| = -Real.log y := abs_of_neg hl
  have := perronT_sub y c T 0
  rw [sub_zero, mul_zero, sub_zero] at this
  rw [this, habs]
  have main : ∀ U : ℝ, c < U →
      ‖VIntegral (F y) c (-T) T‖ ≤ 2 * (y ^ c / (-Real.log y * T)) + 2 * T / U := by
    intro U hU
    have hU0 : 0 < U := by linarith
    have hR := rectangleIntegral_F_right (T := T) hy0 hc hU.le
    simp only [RectangleIntegral] at hR
    have hre1 : ((c : ℂ) - T * I).re = c := by simp
    have him1 : ((c : ℂ) - T * I).im = -T := by simp
    have hre2 : ((U : ℂ) + T * I).re = U := by simp
    have him2 : ((U : ℂ) + T * I).im = T := by simp
    rw [hre1, him1, hre2, him2] at hR
    have hV : VIntegral (F y) c (-T) T =
        HIntegral (F y) c U (-T) - HIntegral (F y) c U T + VIntegral (F y) U (-T) T := by
      linear_combination -hR
    rw [hV]
    have h1 := norm_HIntegral_le hy0 hy.ne (by linarith : c ≤ U) hT.ne'
    have h2 := norm_HIntegral_le hy0 hy.ne (by linarith : c ≤ U) (by linarith : -T ≠ 0)
    have h3 := norm_VIntegral_le hy0 hU0.ne' hT.le
    rw [abs_neg, abs_of_pos hT] at h2
    rw [abs_of_pos hT] at h1
    rw [abs_of_pos hU0] at h3
    have hyU : y ^ U ≤ 1 := Real.rpow_le_one hy0.le hy.le hU0.le
    have hyU0 : 0 < y ^ U := Real.rpow_pos_of_pos hy0 _
    have hlt : 0 < -Real.log y * T := mul_pos (by linarith) hT
    have e1 : (y ^ U - y ^ c) / (Real.log y * T) ≤ y ^ c / (-Real.log y * T) := by
      rw [show (y ^ U - y ^ c) / (Real.log y * T) = (y ^ c - y ^ U) / (-Real.log y * T) by
        rw [← neg_div_neg_eq]; ring_nf]
      exact div_le_div_of_nonneg_right (by linarith) hlt.le
    have e2 : y ^ U / U * (2 * T) ≤ 2 * T / U := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hU0]; nlinarith
    calc _ ≤ ‖HIntegral (F y) c U (-T)‖ + ‖HIntegral (F y) c U T‖ +
          ‖VIntegral (F y) U (-T) T‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ _ := by linarith
  have key : ‖VIntegral (F y) c (-T) T‖ ≤ 2 * (y ^ c / (-Real.log y * T)) := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have := main (c + 4 * T / ε) (by have : 0 < 4 * T / ε := by positivity
                                     linarith)
    have : 2 * T / (c + 4 * T / ε) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      have : 0 < c * ε := mul_pos hc hε
      field_simp
      nlinarith
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ 2 * (y ^ c / (-Real.log y * T)) := key
    _ = _ := by field_simp

/-! ### The `y^c` half: arcs and primitives -/

/-- Fundamental theorem of calculus along a path `γ`, for a primitive `Φ` of `f`. -/
lemma ftc_path {f Φ : ℂ → ℂ} {γ γ' : ℝ → ℂ} {a b : ℝ}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hΦ : ∀ t ∈ uIcc a b, HasDerivAt Φ (f (γ t)) (γ t))
    (hcont : Continuous fun t => f (γ t) * γ' t) :
    ∫ t in a..b, f (γ t) * γ' t = Φ (γ b) - Φ (γ a) :=
  integral_eq_sub_of_hasDerivAt (fun t ht => (hΦ t ht).comp t (hγ t)) (hcont.intervalIntegrable _ _)

lemma hasDerivAt_seg (c t : ℝ) : HasDerivAt (fun t : ℝ => (c : ℂ) + t * I) I t := by
  simpa using (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (c : ℂ)

/-- The point `R e^{iθ}`. -/
def arcPt (R θ : ℝ) : ℂ := (R : ℂ) * exp (θ * I)

lemma hasDerivAt_arcPt (R θ : ℝ) : HasDerivAt (arcPt R) (arcPt R θ * I) θ := by
  unfold arcPt
  have := ((((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp).const_mul (R : ℂ)
  simpa [mul_assoc] using this

lemma arcPt_ne_zero {R : ℝ} (hR : 0 < R) (θ : ℝ) : arcPt R θ ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hR.ne') (exp_ne_zero _)

lemma arcPt_re (R θ : ℝ) : (arcPt R θ).re = R * Real.cos θ := by
  simp [arcPt, exp_ofReal_mul_I_re]

lemma norm_arcPt {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : ‖arcPt R θ‖ = R := by
  simp [arcPt, norm_exp_ofReal_mul_I, abs_of_nonneg hR]

/-- Integral along the arc `θ ↦ R e^{iθ}`. -/
def arcIntegral (f : ℂ → ℂ) (R α β : ℝ) : ℂ := ∫ θ in α..β, f (arcPt R θ) * (arcPt R θ * I)

lemma VIntegral_eq_path (f : ℂ → ℂ) (c T : ℝ) :
    VIntegral f c (-T) T = ∫ t in (-T)..T, f ((fun t : ℝ => (c : ℂ) + t * I) t) * I := by
  rw [VIntegral, ← intervalIntegral.integral_const_mul]
  exact integral_congr fun t _ => by ring

section Geometry

variable {c T : ℝ}

/-- Radius `|c + iT|` and angle `arg (c + iT)`. -/
def rad (c T : ℝ) : ℝ := ‖(c : ℂ) + T * I‖
def ang (c T : ℝ) : ℝ := arg ((c : ℂ) + T * I)

lemma rad_pos (hc : 0 < c) : 0 < rad c T := norm_pos_iff.mpr (ne_zero_of_re hc.ne')

lemma arcPt_ang : arcPt (rad c T) (ang c T) = c + T * I := norm_mul_exp_arg_mul_I _

lemma arcPt_neg_ang : arcPt (rad c T) (-ang c T) = c - T * I := by
  have h := congrArg (starRingEnd ℂ) (arcPt_ang (c := c) (T := T))
  have e : exp (((-ang c T : ℝ) : ℂ) * I) = starRingEnd ℂ (exp ((ang c T : ℂ) * I)) := by
    rw [← exp_conj]; congr 1; simp
  simp only [arcPt, map_mul, conj_ofReal, map_add, conj_I] at h
  rw [arcPt, e, h]; ring

lemma arcPt_ang_sub_two_pi : arcPt (rad c T) (ang c T - 2 * π) = c + T * I := by
  rw [← arcPt_ang]
  simp only [arcPt]
  congr 1
  rw [show (((ang c T - 2 * π : ℝ)) : ℂ) * I = (ang c T : ℂ) * I - 2 * π * I by push_cast; ring,
    Complex.exp_sub, exp_two_pi_mul_I, div_one]

lemma ang_nonneg (hT : 0 ≤ T) : 0 ≤ ang c T := arg_nonneg_iff.mpr (by simpa using hT)

lemma ang_le (hc : 0 < c) : ang c T ≤ π / 2 :=
  (abs_le.mp (abs_arg_le_pi_div_two_iff.mpr (by simpa using hc.le))).2

lemma rad_cos_ang : rad c T * Real.cos (ang c T) = c := by
  rw [← arcPt_re, arcPt_ang]; simp

lemma norm_seg_le {t : ℝ} (ht : |t| ≤ T) : ‖(c : ℂ) + t * I‖ ≤ rad c T := by
  have h1 : ‖(c : ℂ) + t * I‖ = Real.sqrt (c ^ 2 + t ^ 2) := by
    rw [norm_def, normSq_apply]; congr 1; simp; ring
  have h2 : rad c T = Real.sqrt (c ^ 2 + T ^ 2) := by
    rw [rad, norm_def, normSq_apply]; congr 1; simp; ring
  rw [h1, h2]
  apply Real.sqrt_le_sqrt
  nlinarith [abs_nonneg t, sq_abs t]

lemma log_seg (hc : 0 < c) :
    Complex.log ((c : ℂ) + T * I) - Complex.log ((c : ℂ) - T * I) = 2 * ang c T * I := by
  have hconj : (c : ℂ) - T * I = starRingEnd ℂ ((c : ℂ) + T * I) := by simp; ring
  have hne : arg ((c : ℂ) + T * I) ≠ π := by
    have := ang_le (c := c) (T := T) hc
    unfold ang at this; intro h; rw [h] at this; linarith [pi_pos]
  apply Complex.ext
  · simp only [sub_re, log_re, hconj, Complex.norm_conj]; simp
  · simp only [sub_im, log_im, hconj, arg_conj, hne, ↓reduceIte]
    simp [ang]; ring

end Geometry

lemma continuous_G_arc {y R : ℝ} (hy : 0 < y) :
    Continuous fun θ => G y (arcPt R θ) * (arcPt R θ * I) :=
  ((differentiable_G hy).continuous.comp (by unfold arcPt; fun_prop)).mul
    (by unfold arcPt; fun_prop)

lemma continuous_inv_arc {R : ℝ} (hR : 0 < R) :
    Continuous fun θ => 1 / arcPt R θ * (arcPt R θ * I) :=
  (continuous_const.div (by unfold arcPt; fun_prop) (arcPt_ne_zero hR)).mul
    (by unfold arcPt; fun_prop)

lemma arcIntegral_inv {R : ℝ} (hR : 0 < R) (α β : ℝ) :
    arcIntegral (fun s => 1 / s) R α β = (β - α) * I := by
  have h : ∀ θ ∈ uIcc α β, 1 / arcPt R θ * (arcPt R θ * I) = I := fun θ _ => by
    field_simp [arcPt_ne_zero hR θ]
  rw [arcIntegral, integral_congr h, intervalIntegral.integral_const, Complex.real_smul]
  push_cast; ring

lemma arcIntegral_split {y R : ℝ} (hy : 0 < y) (hR : 0 < R) (α β : ℝ) :
    arcIntegral (F y) R α β = arcIntegral (G y) R α β + arcIntegral (fun s => 1 / s) R α β := by
  simp only [arcIntegral]
  rw [← intervalIntegral.integral_add ((continuous_G_arc hy).intervalIntegrable _ _)
    ((continuous_inv_arc hR).intervalIntegrable _ _)]
  exact integral_congr fun θ _ => by
    rw [F_eq_G_add (arcPt_ne_zero hR θ)]; ring

/-- Key identity: the vertical integral of `G` equals any arc integral of `G` with the same ends. -/
lemma VIntegral_G_eq_arc {y c T α β : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hα : arcPt (rad c T) α = c - T * I) (hβ : arcPt (rad c T) β = c + T * I) :
    VIntegral (G y) c (-T) T = arcIntegral (G y) (rad c T) α β := by
  set R := rad c T
  obtain ⟨Φ, hΦ⟩ := (differentiable_G hy).differentiableOn.isExactOn_ball (c := 0) (r := R + 1)
  have hR := rad_pos (c := c) (T := T) hc
  have h1 := ftc_path (f := G y) (Φ := Φ) (γ := fun t : ℝ => (c : ℂ) + t * I) (γ' := fun _ => I)
    (a := -T) (b := T) (hasDerivAt_seg c) (fun t ht => hΦ _ (by
      rw [Metric.mem_ball, dist_zero_right]
      rw [uIcc_of_le (by linarith : -T ≤ T)] at ht
      have : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
      linarith [norm_seg_le (c := c) this]))
    ((differentiable_G hy).continuous.comp (by fun_prop) |>.mul continuous_const)
  have h2 := ftc_path (f := G y) (Φ := Φ) (γ := arcPt R) (γ' := fun θ => arcPt R θ * I)
    (a := α) (b := β) (hasDerivAt_arcPt R) (fun θ _ => hΦ _ (by
      rw [Metric.mem_ball, dist_zero_right, norm_arcPt hR.le]; linarith))
    (continuous_G_arc hy)
  rw [VIntegral_eq_path, h1, arcIntegral, h2, hα, hβ]
  congr 2; push_cast; ring

lemma VIntegral_inv {c T : ℝ} (hc : 0 < c) :
    VIntegral (fun s => 1 / s) c (-T) T = 2 * ang c T * I := by
  have h1 := ftc_path (f := fun s => 1 / s) (Φ := Complex.log)
    (γ := fun t : ℝ => (c : ℂ) + t * I) (γ' := fun _ => I)
    (a := -T) (b := T) (hasDerivAt_seg c) (fun t _ => by
      simpa [one_div] using Complex.hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inl (by simpa using hc))))
    ((continuous_inv_V hc.ne').mul continuous_const)
  rw [VIntegral_eq_path, h1, ← log_seg hc]
  congr 2; push_cast; ring

/-- Arc bound: `‖∫_α^β F(Re^{iθ}) d(Re^{iθ})‖ ≤ |β-α| · B` when `y^{R cos θ} ≤ B` on the arc. -/
lemma norm_arcIntegral_F_le {y R α β B : ℝ} (hy : 0 < y) (hR : 0 < R)
    (hB : ∀ θ ∈ uIcc α β, y ^ (R * Real.cos θ) ≤ B) :
    ‖arcIntegral (F y) R α β‖ ≤ B * |β - α| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro θ hθ
  have hne := arcPt_ne_zero hR θ
  rw [norm_mul, norm_mul, norm_I, mul_one, F, norm_div, norm_cpow_eq_rpow_re_of_pos hy,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hne), arcPt_re]
  exact hB θ (uIoc_subset_uIcc hθ)

lemma cos_ge_cos_ang {θ a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ π) (hθ : θ ∈ uIcc (-a) a) :
    Real.cos a ≤ Real.cos θ := by
  rw [← Real.cos_abs θ]
  have h0 : -a ≤ a := by linarith
  rw [uIcc_of_le h0] at hθ
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) ha (abs_le.mpr hθ)

lemma cos_le_cos_ang {θ a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ π)
    (hθ : θ ∈ uIcc (-a) (a - 2 * π)) : Real.cos θ ≤ Real.cos a := by
  have h0 : a - 2 * π ≤ -a := by linarith
  rw [uIcc_of_ge h0] at hθ
  obtain ⟨h1, h2⟩ := hθ
  rw [← Real.cos_neg θ]
  by_cases hu : -θ ≤ π
  · exact Real.cos_le_cos_of_nonneg_of_le_pi ha0 hu (by linarith)
  · rw [← Real.cos_two_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ha0 (by linarith) (by linarith)

/-- **Truncated Perron, single term, `y > 1`, trivial bound.** -/
theorem perron_gt_one' {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronT y c T - 1‖ ≤ y ^ c := by
  have hy0 : 0 < y := by linarith
  have hR := rad_pos (c := c) (T := T) hc
  have ha0 := ang_nonneg (c := c) hT.le
  have ha := ang_le (c := c) (T := T) hc
  set R := rad c T
  set a := ang c T
  have hV : VIntegral (F y) c (-T) T - 2 * π * I = arcIntegral (F y) R (-a) (a - 2 * π) := by
    rw [VIntegral_split hy0 hc.ne', VIntegral_inv hc,
      VIntegral_G_eq_arc hy0 hc hT arcPt_neg_ang arcPt_ang_sub_two_pi,
      arcIntegral_split hy0 hR, arcIntegral_inv hR]
    push_cast; ring
  rw [perronT_sub, mul_one, hV, div_le_iff₀ (by positivity)]
  refine (norm_arcIntegral_F_le hy0 hR (B := y ^ c) fun θ hθ => ?_).trans ?_
  · apply Real.rpow_le_rpow_of_exponent_le hy.le
    rw [← rad_cos_ang (c := c) (T := T)]
    exact mul_le_mul_of_nonneg_left (cos_le_cos_ang ha0 (by linarith [pi_pos]) hθ) hR.le
  · rw [abs_of_nonpos (by linarith [pi_pos])]
    have := Real.rpow_pos_of_pos hy0 c
    nlinarith

/-- **Truncated Perron, single term, `0 < y < 1`, trivial bound.** -/
theorem perron_lt_one' {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronT y c T‖ ≤ y ^ c / 2 := by
  have hR := rad_pos (c := c) (T := T) hc
  have ha0 := ang_nonneg (c := c) hT.le
  have ha := ang_le (c := c) (T := T) hc
  set R := rad c T
  set a := ang c T
  have hV : VIntegral (F y) c (-T) T = arcIntegral (F y) R (-a) a := by
    rw [VIntegral_split hy0 hc.ne', VIntegral_inv hc,
      VIntegral_G_eq_arc hy0 hc hT arcPt_neg_ang arcPt_ang,
      arcIntegral_split hy0 hR, arcIntegral_inv hR]
    push_cast; ring
  have := perronT_sub y c T 0
  rw [sub_zero, mul_zero, sub_zero] at this
  rw [this, hV, div_le_iff₀ (by positivity)]
  refine (norm_arcIntegral_F_le hy0 hR (B := y ^ c) fun θ hθ => ?_).trans ?_
  · apply Real.rpow_le_rpow_of_exponent_ge hy0 hy.le
    rw [← rad_cos_ang (c := c) (T := T)]
    exact mul_le_mul_of_nonneg_left (cos_ge_cos_ang ha0 (by linarith [pi_pos]) hθ) hR.le
  · rw [abs_of_nonneg (by linarith)]
    have := Real.rpow_pos_of_pos hy0 c
    nlinarith [pi_pos]

/-- **Montgomery–Vaughan Lemma 5.1 (single term).** For `c > 0`, `T > 0`, `y > 0`, `y ≠ 1`:
`|(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds - 1_{y>1}| ≤ y^c · min(1, 1/(π T |log y|))`. -/
theorem perron_single {y c T : ℝ} (hy0 : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronT y c T - (if 1 < y then 1 else 0)‖ ≤
      y ^ c * min 1 (1 / (π * T * |Real.log y|)) := by
  have hyc := Real.rpow_pos_of_pos hy0 c
  rcases lt_or_gt_of_ne hy1 with hy | hy
  · simp only [show ¬ 1 < y by linarith, ↓reduceIte]
    rw [sub_zero,
      mul_min_of_nonneg _ _ hyc.le, mul_one, le_min_iff]
    refine ⟨(perron_lt_one' hy0 hy hc hT).trans (by linarith), ?_⟩
    rw [mul_one_div]; exact perron_lt_one hy0 hy hc hT
  · simp only [hy, ↓reduceIte]
    rw [mul_min_of_nonneg _ _ hyc.le, mul_one, le_min_iff,
      abs_of_pos (Real.log_pos hy), mul_one_div]
    exact ⟨perron_gt_one' hy hc hT, perron_gt_one hy hc hT⟩

end

end TruncPerron
