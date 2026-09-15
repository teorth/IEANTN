/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section6Zeros

/-!
# Section 7: the weight at a zero on the critical line (`cor:thonny`)

For `s = 1/2 + it`, `ω⁺_{T,σ}(s) + ξ i θ_{T,1}(s)` is compared

* with `F(t/T) + ξ(1 - t/T) i` for `0 < t < T` (eq. `witdim`), error
  `|σ - 1/2| T/(π t²) + (2.78|σ - 1/2| + 1)/T`;
* with the classical `iT/((s - σ)π)` for `0 < t ≤ T/2` (eq. `demoscen`), error
  `1 + (2.78|σ - 1/2| + 1)/T`.

`F = CH2Section7.Fc`, and the inputs are `lem:sibelius` (b), (c) from `Section7.lean`. The paper states
(`witdim`) for `0 < t ≤ T`; the endpoint `t = T` is excluded here because `Fc 1` is a junk value, and
costs nothing downstream since `T` is chosen free of zero ordinates.
-/

open Complex

namespace CH2Section6

theorem Fc_ofReal (x : ℝ) : CH2Section7.Fc (x : ℂ) = ((CH2Section7.Fweight x : ℝ) : ℂ) := by
  unfold CH2Section7.Fc CH2Section7.Fweight
  push_cast
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_cot]

/-- `ω⁺ = F((s - σ)/(iT)) + (c_{T,σ} - 1/π)`. -/
theorem omegaPlus_eq_Fc (T σ : ℝ) (s : ℂ) :
    omegaPlus T σ s = CH2Section7.Fc ((s - σ) / (I * T)) + (cTS T σ - 1 / (Real.pi : ℂ)) := by
  unfold omegaPlus CH2Section7.Fc thetaTS
  ring

/-- `|c_{T,σ} - 1/π| ≤ |σ - 1|/T`, from `1 ≤ u coth u ≤ 1 + u`. -/
theorem norm_cTS_sub_le {T σ : ℝ} (hT : 0 < T) (hσ1 : σ ≠ 1) :
    ‖cTS T σ - 1 / (Real.pi : ℂ)‖ ≤ |σ - 1| / T := by
  have hπ := Real.pi_pos
  set u : ℝ := Real.pi * (1 - σ) / T with hu
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hθ : thetaTS T σ (1 + I * T) = I * (((1 - σ) / T : ℝ) : ℂ) := by
    unfold thetaTS
    push_cast
    field_simp
    ring_nf
    try simp only [I_sq]
    try ring
  have hc : cTS T σ = (((1 / Real.pi) * (u * (Real.cosh u / Real.sinh u)) : ℝ) : ℂ) := by
    unfold cTS
    rw [hθ, show (Real.pi : ℂ) * (I * (((1 - σ) / T : ℝ) : ℂ)) = I * (u : ℂ) by
      rw [hu]; push_cast; ring, cot_I_mul, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    rw [hu]
    push_cast
    field_simp
    ring_nf
    try simp only [I_sq]
    try ring
  rw [hc, show (1 / (Real.pi : ℂ)) = ((1 / Real.pi : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have hu0 : u ≠ 0 := by
    rw [hu]; apply div_ne_zero (mul_ne_zero hπ.ne' (sub_ne_zero.mpr (Ne.symm hσ1))) hT.ne'
  -- `u coth u` is even
  have heven : u * (Real.cosh u / Real.sinh u) = |u| * (Real.cosh |u| / Real.sinh |u|) := by
    rcases lt_or_gt_of_ne hu0 with h | h
    · rw [abs_of_neg h, Real.cosh_neg, Real.sinh_neg]; field_simp
    · rw [abs_of_pos h]
  have hup : 0 < |u| := abs_pos.mpr hu0
  have h1 := CH2Section7.inv_le_coth hup
  have h2 := CH2Section7.coth_le_one_add_inv hup
  have hlow : 1 ≤ |u| * (Real.cosh |u| / Real.sinh |u|) := by
    have := mul_le_mul_of_nonneg_left h1 hup.le
    rwa [mul_one_div_cancel hup.ne'] at this
  have hhigh : |u| * (Real.cosh |u| / Real.sinh |u|) ≤ |u| + 1 := by
    have := mul_le_mul_of_nonneg_left h2 hup.le
    rwa [mul_add, mul_one, mul_one_div_cancel hup.ne'] at this
  rw [heven, show 1 / Real.pi * (|u| * (Real.cosh |u| / Real.sinh |u|)) - 1 / Real.pi
      = (|u| * (Real.cosh |u| / Real.sinh |u|) - 1) / Real.pi by ring,
    abs_div, abs_of_pos hπ, abs_of_nonneg (by linarith), div_le_iff₀ hπ]
  have hua : |u| = Real.pi * |σ - 1| / T := by
    rw [hu, abs_div, abs_mul, abs_of_pos hπ, abs_of_pos hT, abs_sub_comm]
  rw [hua] at hhigh ⊢
  have : |σ - 1| / T * Real.pi = Real.pi * |σ - 1| / T := by ring
  linarith

/-- The point `(s - σ)/(iT)` for `s = 1/2 + it`. -/
theorem zpt_eq {T σ t : ℝ} (hT : 0 < T) :
    ((1 / 2 + (t : ℂ) * I) - σ) / (I * T) = ((t / T : ℝ) : ℂ) + (((σ - 1 / 2) / T : ℝ) : ℂ) * I := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  push_cast
  field_simp
  ring_nf
  try simp only [I_sq]
  try ring

theorem theta1_eq {T t : ℝ} (hT : 0 < T) (ξ : ℝ) :
    (ξ : ℂ) * I * thetaTS T 1 (1 / 2 + (t : ℂ) * I)
      = (ξ : ℂ) * (((1 - t / T) : ℝ) : ℂ) * I + ((ξ / (2 * T) : ℝ) : ℂ) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  unfold thetaTS
  push_cast
  field_simp
  ring_nf
  try simp only [I_sq]
  try ring

/-- **`cor:thonny`, eq. `witdim`.** -/
theorem thonny_witdim (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {T σ ξ t : ℝ} (hT : 0 < T) (hσ1 : σ ≠ 1) (hσT : |σ - 1 / 2| ≤ T / 2) (hξ : |ξ| ≤ 1)
    (ht0 : 0 < t) (htT : t < T) :
    ‖omegaPlus T σ (1 / 2 + (t : ℂ) * I) + (ξ : ℂ) * I * thetaTS T 1 (1 / 2 + (t : ℂ) * I)
        - (((CH2Section7.Fweight (t / T) : ℝ) : ℂ) + (ξ : ℂ) * (((1 - t / T) : ℝ) : ℂ) * I)‖
      ≤ |σ - 1 / 2| * T / (Real.pi * t ^ 2) + (2.78 * |σ - 1 / 2| + 1) / T := by
  have hπ := Real.pi_pos
  set x : ℝ := t / T with hx
  set y : ℝ := (σ - 1 / 2) / T with hy
  have hx0 : 0 < x := div_pos ht0 hT
  have hx1 : x < 1 := (div_lt_one hT).mpr htT
  have hy2 : |y| ≤ 1 / 2 := by
    rw [hy, abs_div, abs_of_pos hT, div_le_iff₀ hT]; linarith
  rw [omegaPlus_eq_Fc, zpt_eq hT, theta1_eq hT, ← hx, ← hy, ← Fc_ofReal]
  have e : CH2Section7.Fc ((x : ℂ) + (y : ℂ) * I) + (cTS T σ - 1 / (Real.pi : ℂ))
        + ((ξ : ℂ) * ((1 - x : ℝ) : ℂ) * I + ((ξ / (2 * T) : ℝ) : ℂ))
        - (CH2Section7.Fc (x : ℂ) + (ξ : ℂ) * ((1 - x : ℝ) : ℂ) * I)
      = (CH2Section7.Fc ((x : ℂ) + (y : ℂ) * I) - CH2Section7.Fc (x : ℂ))
        + (cTS T σ - 1 / (Real.pi : ℂ)) + ((ξ / (2 * T) : ℝ) : ℂ) := by ring
  rw [e]
  have hb := CH2Section7.sibelius_b hcs hx0 hx1 hy2
  have hnx : x ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := by
    rw [Complex.norm_add_mul_I]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg y])
  have hb' : |y| / (Real.pi * x * ‖(x : ℂ) + (y : ℂ) * I‖) ≤ |y| / (Real.pi * x ^ 2) := by
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hnx (by positivity)
  have hc := norm_cTS_sub_le hT hσ1
  have hξn : ‖((ξ / (2 * T) : ℝ) : ℂ)‖ ≤ 1 / (2 * T) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 2 * T)]
    exact div_le_div_of_nonneg_right hξ (by positivity)
  have hσ : |σ - 1| ≤ |σ - 1 / 2| + 1 / 2 := by
    calc |σ - 1| = |(σ - 1 / 2) + (-(1 / 2))| := by ring_nf
      _ ≤ |σ - 1 / 2| + |-(1 / 2 : ℝ)| := abs_add_le _ _
      _ = |σ - 1 / 2| + 1 / 2 := by norm_num
  have hyv : |y| = |σ - 1 / 2| / T := by rw [hy, abs_div, abs_of_pos hT]
  have hkey1 : |y| / (Real.pi * x ^ 2) = |σ - 1 / 2| * T / (Real.pi * t ^ 2) := by
    rw [hyv, hx]; field_simp
  calc _ ≤ ‖CH2Section7.Fc ((x : ℂ) + (y : ℂ) * I) - CH2Section7.Fc (x : ℂ)‖
        + ‖cTS T σ - 1 / (Real.pi : ℂ)‖ + ‖((ξ / (2 * T) : ℝ) : ℂ)‖ := norm_add₃_le
    _ ≤ (|y| / (Real.pi * x ^ 2) + 1.78 * |y|) + |σ - 1| / T + 1 / (2 * T) := by
        gcongr; linarith
    _ ≤ |σ - 1 / 2| * T / (Real.pi * t ^ 2) + (2.78 * |σ - 1 / 2| + 1) / T := by
        rw [hkey1, hyv]
        have : |σ - 1| / T ≤ (|σ - 1 / 2| + 1 / 2) / T := div_le_div_of_nonneg_right hσ hT.le
        have e2 : 1.78 * (|σ - 1 / 2| / T) + (|σ - 1 / 2| + 1 / 2) / T + 1 / (2 * T)
            = (2.78 * |σ - 1 / 2| + 1) / T := by field_simp; ring
        linarith

/-- **`cor:thonny`, eq. `demoscen`.** -/
theorem thonny_demoscen (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {T σ ξ t : ℝ} (hT : 0 < T) (hσ1 : σ ≠ 1) (hσT : |σ - 1 / 2| ≤ T / 2) (hξ : |ξ| ≤ 1)
    (ht0 : 0 < t) (htT : t ≤ T / 2) :
    ‖omegaPlus T σ (1 / 2 + (t : ℂ) * I) + (ξ : ℂ) * I * thetaTS T 1 (1 / 2 + (t : ℂ) * I)
        - I * T / (((1 / 2 + (t : ℂ) * I) - σ) * Real.pi)‖
      ≤ 1 + (2.78 * |σ - 1 / 2| + 1) / T := by
  have hπ := Real.pi_pos
  set x : ℝ := t / T with hx
  set y : ℝ := (σ - 1 / 2) / T with hy
  have hx0 : 0 < x := div_pos ht0 hT
  have hx2 : x ≤ 1 / 2 := by rw [hx, div_le_iff₀ hT]; linarith
  have hy2 : |y| ≤ 1 / 2 := by
    rw [hy, abs_div, abs_of_pos hT, div_le_iff₀ hT]; linarith
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
  have hsσ : ((1 / 2 + (t : ℂ) * I) - σ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hz0 : ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hinv : I * T / (((1 / 2 + (t : ℂ) * I) - σ) * Real.pi)
      = 1 / ((Real.pi : ℂ) * ((x : ℂ) + (y : ℂ) * I)) := by
    rw [← zpt_eq hT]
    field_simp
  rw [omegaPlus_eq_Fc, zpt_eq hT, theta1_eq hT, ← hx, ← hy, hinv]
  have e : CH2Section7.Fc ((x : ℂ) + (y : ℂ) * I) + (cTS T σ - 1 / (Real.pi : ℂ))
        + ((ξ : ℂ) * ((1 - x : ℝ) : ℂ) * I + ((ξ / (2 * T) : ℝ) : ℂ))
        - 1 / ((Real.pi : ℂ) * ((x : ℂ) + (y : ℂ) * I))
      = (CH2Section7.Acomp ((x : ℂ) + (y : ℂ) * I) - CH2Section7.Acomp (x : ℂ))
        + (CH2Section7.Acomp (x : ℂ) + (ξ : ℂ) * ((1 - x : ℝ) : ℂ) * I)
        + (cTS T σ - 1 / (Real.pi : ℂ)) + ((ξ / (2 * T) : ℝ) : ℂ) := by
    unfold CH2Section7.Acomp; ring
  rw [e]
  obtain ⟨hA, hAd⟩ := CH2Section7.sibelius_c hcs hx0 hx2 hy2
  -- `A(x)` is real, so `|A(x) + ξ(1-x)i| ≤ √((π/3)² x² + (1-x)²) ≤ 1`
  have hAreal : CH2Section7.Acomp (x : ℂ)
      = ((CH2Section7.Fweight x - 1 / (Real.pi * x) : ℝ) : ℂ) := by
    unfold CH2Section7.Acomp; rw [Fc_ofReal]; push_cast; ring
  have hmid : ‖CH2Section7.Acomp (x : ℂ) + (ξ : ℂ) * ((1 - x : ℝ) : ℂ) * I‖ ≤ 1 := by
    rw [hAreal] at hA ⊢
    rw [show ((CH2Section7.Fweight x - 1 / (Real.pi * x) : ℝ) : ℂ) + (ξ : ℂ) * ((1 - x : ℝ) : ℂ) * I
        = ((CH2Section7.Fweight x - 1 / (Real.pi * x) : ℝ) : ℂ) + ((ξ * (1 - x) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_add_mul_I]
    rw [Complex.norm_real, Real.norm_eq_abs] at hA
    apply Real.sqrt_le_one.mpr
    have h1 : (CH2Section7.Fweight x - 1 / (Real.pi * x)) ^ 2 ≤ (Real.pi / 3 * x) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
    have h2 : (ξ * (1 - x)) ^ 2 ≤ (1 - x) ^ 2 := by
      rw [mul_pow]
      have : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
      nlinarith [sq_nonneg (1 - x)]
    have hπ2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2]
    have h4 : x * (Real.pi ^ 2 * x / 9 + x - 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hx0.le (by nlinarith)
    have h3 : (Real.pi / 3 * x) ^ 2 + (1 - x) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hc := norm_cTS_sub_le hT hσ1
  have hξn : ‖((ξ / (2 * T) : ℝ) : ℂ)‖ ≤ 1 / (2 * T) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 2 * T)]
    exact div_le_div_of_nonneg_right hξ (by positivity)
  have hσ : |σ - 1| ≤ |σ - 1 / 2| + 1 / 2 := by
    calc |σ - 1| = |(σ - 1 / 2) + (-(1 / 2))| := by ring_nf
      _ ≤ |σ - 1 / 2| + |-(1 / 2 : ℝ)| := abs_add_le _ _
      _ = |σ - 1 / 2| + 1 / 2 := by norm_num
  have hyv : |y| = |σ - 1 / 2| / T := by rw [hy, abs_div, abs_of_pos hT]
  calc _ ≤ ‖CH2Section7.Acomp ((x : ℂ) + (y : ℂ) * I) - CH2Section7.Acomp (x : ℂ)‖
        + ‖CH2Section7.Acomp (x : ℂ) + (ξ : ℂ) * ((1 - x : ℝ) : ℂ) * I‖
        + ‖cTS T σ - 1 / (Real.pi : ℂ)‖ + ‖((ξ / (2 * T) : ℝ) : ℂ)‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add₃_le
    _ ≤ 1.78 * |y| + 1 + |σ - 1| / T + 1 / (2 * T) := by gcongr
    _ ≤ 1 + (2.78 * |σ - 1 / 2| + 1) / T := by
        rw [hyv]
        have : |σ - 1| / T ≤ (|σ - 1 / 2| + 1 / 2) / T := div_le_div_of_nonneg_right hσ hT.le
        have e2 : 1.78 * (|σ - 1 / 2| / T) + (|σ - 1 / 2| + 1 / 2) / T + 1 / (2 * T)
            = (2.78 * |σ - 1 / 2| + 1) / T := by field_simp; ring
        linarith

end CH2Section6
