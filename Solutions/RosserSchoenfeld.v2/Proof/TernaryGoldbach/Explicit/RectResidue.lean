import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.DSlope
import TernaryGoldbach.Explicit.Landau

/-!
# Residues on rectangles

`rectInt f z w` is the boundary integral of `f` around the rectangle with corners `z`, `w`
(Mathlib's convention in `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).
* `rectInt_inv_sub`: `∮ ds/(s − ρ) = 2πi` for `ρ` strictly inside (antiderivatives `log(s − ρ)` on
  three sides and `log(ρ − s)` on the left side, and `arg p − arg(−p) = ±π`);
* `rectInt_div_sub`: Cauchy's formula `∮ g(s)/(s − ρ) ds = 2πi g(ρ)`.
-/

open Complex Set MeasureTheory intervalIntegral Metric
open scoped Real Interval

namespace TernaryGoldbach.Explicit

/-- The boundary integral around the rectangle `[z.re, w.re] × [z.im, w.im]`. -/
noncomputable def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- `∫_a^b dx/(x + κ) = log(b + κ) − log(a + κ)` if the segment avoids the slit. -/
theorem integral_inv_add_real {a b : ℝ} {κ : ℂ} (h : ∀ x ∈ [[a, b]], (x : ℂ) + κ ∈ slitPlane) :
    ∫ x : ℝ in a..b, ((x : ℂ) + κ)⁻¹ = Complex.log (b + κ) - Complex.log (a + κ) := by
  have hd : ∀ x ∈ [[a, b]], HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + κ)) ((x : ℂ) + κ)⁻¹ x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + κ) 1 x := (hasDerivAt_id x).ofReal_comp.add_const κ
    have := h1.clog_real (h x hx)
    simpa using this
  have hc : ContinuousOn (fun x : ℝ => ((x : ℂ) + κ)⁻¹) [[a, b]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    exact slitPlane_ne_zero (h x hx)
  exact integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)

/-- `∫_c^d dy/(σ + iy + κ) = −i (log(σ + id + κ) − log(σ + ic + κ))` if the segment avoids the slit. -/
theorem integral_inv_add_imag {c d σ : ℝ} {κ : ℂ}
    (h : ∀ y ∈ [[c, d]], (σ : ℂ) + y * I + κ ∈ slitPlane) :
    ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
      -I * (Complex.log (σ + d * I + κ) - Complex.log (σ + c * I + κ)) := by
  have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log ((σ : ℂ) + y * I + κ))
      ((σ : ℂ) + y * I + κ)⁻¹ y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => (σ : ℂ) + y * I + κ) I y := by
      have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ) |>.add_const κ
      simpa using this
    have := (h1.clog_real (h y hy)).const_mul (-I)
    refine this.congr_deriv ?_
    have hne := slitPlane_ne_zero (h y hy)
    field_simp
    rw [I_sq]; ring
  have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    exact slitPlane_ne_zero (h y hy)
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- Same with `log(−·)`: for segments in the left half-plane. -/
theorem integral_inv_add_imag_neg {c d σ : ℝ} {κ : ℂ}
    (h : ∀ y ∈ [[c, d]], -((σ : ℂ) + y * I + κ) ∈ slitPlane) :
    ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
      -I * (Complex.log (-((σ : ℂ) + d * I + κ)) - Complex.log (-((σ : ℂ) + c * I + κ))) := by
  have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log (-((σ : ℂ) + y * I + κ)))
      ((σ : ℂ) + y * I + κ)⁻¹ y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => -((σ : ℂ) + y * I + κ)) (-I) y :=
      ((((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ)).add_const κ).neg.congr_deriv
        (by simp)
    have := (h1.clog_real (h y hy)).const_mul (-I)
    refine this.congr_deriv ?_
    have hne : (σ : ℂ) + y * I + κ ≠ 0 := by
      intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
    field_simp
    rw [I_sq]; ring
  have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

theorem log_sub_log_neg_of_im_pos {p : ℂ} (hp : 0 < p.im) :
    Complex.log p - Complex.log (-p) = π * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hp]
  push_cast; ring

theorem log_sub_log_neg_of_im_neg {p : ℂ} (hp : p.im < 0) :
    Complex.log p - Complex.log (-p) = -(π * I) := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hp]
  push_cast; ring

/-- **`∮ ds/(s − ρ) = 2πi`** for `ρ` strictly inside the rectangle. -/
theorem rectInt_inv_sub {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
    (h4 : ρ.im < w.im) : rectInt (fun s => (s - ρ)⁻¹) z w = 2 * π * I := by
  unfold rectInt
  -- bottom and top
  have hB : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - ρ)⁻¹ =
      Complex.log (w.re + (z.im * I - ρ)) - Complex.log (z.re + (z.im * I - ρ)) := by
    have := integral_inv_add_real (a := z.re) (b := w.re) (κ := z.im * I - ρ) (fun x _ => by
      refine Or.inr ?_
      simp; linarith)
    simpa [add_sub_assoc] using this
  have hT : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - ρ)⁻¹ =
      Complex.log (w.re + (w.im * I - ρ)) - Complex.log (z.re + (w.im * I - ρ)) := by
    have := integral_inv_add_real (a := z.re) (b := w.re) (κ := w.im * I - ρ) (fun x _ => by
      refine Or.inr ?_
      simp; linarith)
    simpa [add_sub_assoc] using this
  have hR : ∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - ρ)⁻¹ =
      -I * (Complex.log (w.re + w.im * I + -ρ) - Complex.log (w.re + z.im * I + -ρ)) := by
    have := integral_inv_add_imag (c := z.im) (d := w.im) (σ := w.re) (κ := -ρ) (fun y _ => by
      refine Or.inl ?_
      simp; linarith)
    simpa [sub_eq_add_neg] using this
  have hL : ∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - ρ)⁻¹ =
      -I * (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) := by
    have := integral_inv_add_imag_neg (c := z.im) (d := w.im) (σ := z.re) (κ := -ρ) (fun y _ => by
      refine Or.inl ?_
      simp; linarith)
    simpa [sub_eq_add_neg] using this
  simp only [smul_eq_mul]
  rw [hB, hT, hR, hL]
  have eTL : Complex.log ((z.re : ℂ) + (w.im * I - ρ)) - Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) =
      π * I := by
    have hp : 0 < ((z.re : ℂ) + (w.im * I - ρ)).im := by simp; linarith
    rw [← log_sub_log_neg_of_im_pos hp]; congr 2; ring
  have eBL : Complex.log ((z.re : ℂ) + (z.im * I - ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ)) =
      -(π * I) := by
    have hp : ((z.re : ℂ) + (z.im * I - ρ)).im < 0 := by simp; linarith
    rw [← log_sub_log_neg_of_im_neg hp]; congr 2; ring
  have e1 : Complex.log ((w.re : ℂ) + w.im * I + -ρ) = Complex.log ((w.re : ℂ) + (w.im * I - ρ)) := by
    congr 1; ring
  have e2 : Complex.log ((w.re : ℂ) + z.im * I + -ρ) = Complex.log ((w.re : ℂ) + (z.im * I - ρ)) := by
    congr 1; ring
  rw [e1, e2]
  have hII : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
  linear_combination eTL - eBL + (Complex.log ((w.re : ℂ) + (w.im * I - ρ)) -
    Complex.log ((w.re : ℂ) + (z.im * I - ρ))) * hII -
    (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) * hII

/-! ## Cauchy's formula on rectangles -/

theorem mem_rect_boundary_ne {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
    (h4 : ρ.im < w.im) :
    (∀ x : ℝ, (x : ℂ) + z.im * I ≠ ρ) ∧ (∀ x : ℝ, (x : ℂ) + w.im * I ≠ ρ) ∧
      (∀ y : ℝ, (w.re : ℂ) + y * I ≠ ρ) ∧ (∀ y : ℝ, (z.re : ℂ) + y * I ≠ ρ) := by
  refine ⟨fun x h => ?_, fun x h => ?_, fun y h => ?_, fun y h => ?_⟩
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

/-- `rectInt` is additive (for functions continuous on the boundary). -/
theorem rectInt_add {f g : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hg : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  have hseg1 : ∀ c ∈ [[z.im, w.im]], ∀ φ : ℂ → ℂ,
      ContinuousOn φ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) →
      IntervalIntegrable (fun x : ℝ => φ (x + c * I)) volume z.re w.re := by
    intro c hc φ hφ
    refine ContinuousOn.intervalIntegrable ?_
    refine hφ.comp (by fun_prop) fun x hx => ?_
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨hx, hc⟩
  have hseg2 : ∀ c ∈ [[z.re, w.re]], ∀ φ : ℂ → ℂ,
      ContinuousOn φ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) →
      IntervalIntegrable (fun y : ℝ => φ (c + y * I)) volume z.im w.im := by
    intro c hc φ hφ
    refine ContinuousOn.intervalIntegrable ?_
    refine hφ.comp (by fun_prop) fun y hy => ?_
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨hc, hy⟩
  have lz : z.im ∈ [[z.im, w.im]] := left_mem_uIcc
  have lw : w.im ∈ [[z.im, w.im]] := right_mem_uIcc
  have rz : z.re ∈ [[z.re, w.re]] := left_mem_uIcc
  have rw' : w.re ∈ [[z.re, w.re]] := right_mem_uIcc
  unfold rectInt
  rw [integral_add (hseg1 _ lz f hf) (hseg1 _ lz g hg), integral_add (hseg1 _ lw f hf) (hseg1 _ lw g hg),
    integral_add (hseg2 _ rw' f hf) (hseg2 _ rw' g hg), integral_add (hseg2 _ rz f hf) (hseg2 _ rz g hg)]
  simp only [smul_eq_mul]
  ring

theorem rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectInt (fun s => c * f s) z w = c * rectInt f z w := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- `rectInt` is additive when all eight boundary integrals exist. -/
theorem rectInt_add_of_integrable {f g : ℂ → ℂ} {z w : ℂ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re)
    (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im)
    (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im)
    (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re)
    (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * I)) volume z.im w.im)
    (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * I)) volume z.im w.im) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  unfold rectInt
  rw [integral_add hf1 hg1, integral_add hf2 hg2, integral_add hf3 hg3, integral_add hf4 hg4]
  simp only [smul_eq_mul]
  ring

theorem rectInt_congr {f g : ℂ → ℂ} {z w : ℂ}
    (h1 : ∀ x : ℝ, f (x + z.im * I) = g (x + z.im * I)) (h2 : ∀ x : ℝ, f (x + w.im * I) = g (x + w.im * I))
    (h3 : ∀ y : ℝ, f (w.re + y * I) = g (w.re + y * I)) (h4 : ∀ y : ℝ, f (z.re + y * I) = g (z.re + y * I)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  simp only [h1, h2, h3, h4]

/-- Continuous functions are integrable along the four sides. -/
theorem rect_sides_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
    refine hf.comp (by fun_prop) fun t ht => ?_ <;>
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
  · exact ⟨ht, left_mem_uIcc⟩
  · exact ⟨ht, right_mem_uIcc⟩
  · exact ⟨right_mem_uIcc, ht⟩
  · exact ⟨left_mem_uIcc, ht⟩

/-- `(s − ρ)⁻¹` is integrable along the sides when `ρ` is strictly inside. -/
theorem rect_sides_integrable_inv {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re)
    (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    IntervalIntegrable (fun x : ℝ => ((x + z.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => ((x + w.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => ((w.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => ((z.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im := by
  obtain ⟨b1, b2, b3, b4⟩ := mem_rect_boundary_ne h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
    refine ContinuousOn.inv₀ (by fun_prop) fun t _ => sub_ne_zero.2 ?_
  exacts [b1 t, b2 t, b3 t, b4 t]

/-- **Cauchy's formula on a rectangle**: `∮ g(s)/(s − ρ) ds = 2πi g(ρ)` for `ρ` strictly inside and
`g` holomorphic on an open set containing the closed rectangle. -/
theorem rectInt_mul_inv_sub {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z w ρ : ℂ}
    (hsub : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U) (hg : DifferentiableOn ℂ g U)
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectInt (fun s => g s * (s - ρ)⁻¹) z w = 2 * π * I * g ρ := by
  set R := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hR
  have hρU : ρ ∈ U := hsub (mem_reProdIm.2 ⟨Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩),
    Set.mem_uIcc.2 (Or.inl ⟨h3.le, h4.le⟩)⟩)
  have hgρ : DifferentiableAt ℂ g ρ := hg.differentiableAt (hU.mem_nhds hρU)
  have hdc : ContinuousOn (dslope g ρ) R := by
    intro s hs
    by_cases hsρ : s = ρ
    · subst hsρ; exact (continuousAt_dslope_same.2 hgρ).continuousWithinAt
    · have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hs))
      exact ((differentiableAt_dslope_of_ne hsρ).2 hgs).continuousAt.continuousWithinAt
  have hdd : ∀ s ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ {ρ},
      DifferentiableAt ℂ (dslope g ρ) s := by
    intro s hs
    have hsR : s ∈ R := ⟨Ioo_subset_Icc_self hs.1.1, Ioo_subset_Icc_self hs.1.2⟩
    have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hsR))
    exact (differentiableAt_dslope_of_ne hs.2).2 hgs
  have h0 : rectInt (dslope g ρ) z w = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (dslope g ρ)
      z w {ρ} (countable_singleton ρ) hdc hdd
  obtain ⟨b1, b2, b3, b4⟩ := mem_rect_boundary_ne h1 h2 h3 h4
  have hpt : ∀ s, s ≠ ρ → g s * (s - ρ)⁻¹ = dslope g ρ s + g ρ * (s - ρ)⁻¹ := by
    intro s hs
    rw [dslope_of_ne _ hs, slope_def_field]
    have : s - ρ ≠ 0 := sub_ne_zero.2 hs
    field_simp
    ring
  rw [rectInt_congr (g := fun s => dslope g ρ s + g ρ * (s - ρ)⁻¹)
    (fun x => hpt _ (b1 x)) (fun x => hpt _ (b2 x)) (fun y => hpt _ (b3 y)) (fun y => hpt _ (b4 y))]
  obtain ⟨d1, d2, d3, d4⟩ := rect_sides_integrable hdc
  obtain ⟨i1, i2, i3, i4⟩ := rect_sides_integrable_inv h1 h2 h3 h4
  rw [rectInt_add_of_integrable d1 d2 d3 d4 (i1.const_mul _) (i2.const_mul _) (i3.const_mul _)
    (i4.const_mul _), h0, zero_add, rectInt_const_mul, rectInt_inv_sub h1 h2 h3 h4]
  ring

/-! ## Integrability along the sides, and the residue theorem for `f'/f · h` -/

theorem rectInt_congr' {f g : ℂ → ℂ} {z w : ℂ}
    (h1 : ∀ x ∈ [[z.re, w.re]], f (x + z.im * I) = g (x + z.im * I))
    (h2 : ∀ x ∈ [[z.re, w.re]], f (x + w.im * I) = g (x + w.im * I))
    (h3 : ∀ y ∈ [[z.im, w.im]], f (w.re + y * I) = g (w.re + y * I))
    (h4 : ∀ y ∈ [[z.im, w.im]], f (z.re + y * I) = g (z.re + y * I)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  rw [integral_congr (fun x hx => h1 x hx), integral_congr (fun x hx => h2 x hx),
    integral_congr (fun y hy => h3 y hy), integral_congr (fun y hy => h4 y hy)]

/-- `F` is integrable along the four sides of the rectangle. -/
def RectIntegrable (F : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => F (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => F (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => F (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => F (z.re + y * I)) volume z.im w.im

theorem RectIntegrable.add {F G : ℂ → ℂ} {z w : ℂ} (hF : RectIntegrable F z w)
    (hG : RectIntegrable G z w) : RectIntegrable (fun s => F s + G s) z w :=
  ⟨hF.1.add hG.1, hF.2.1.add hG.2.1, hF.2.2.1.add hG.2.2.1, hF.2.2.2.add hG.2.2.2⟩

theorem RectIntegrable.const_mul {F : ℂ → ℂ} {z w : ℂ} (hF : RectIntegrable F z w) (c : ℂ) :
    RectIntegrable (fun s => c * F s) z w :=
  ⟨hF.1.const_mul c, hF.2.1.const_mul c, hF.2.2.1.const_mul c, hF.2.2.2.const_mul c⟩

theorem rectIntegrable_of_continuousOn {F : ℂ → ℂ} {z w : ℂ}
    (hF : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : RectIntegrable F z w :=
  rect_sides_integrable hF

theorem rectInt_add' {F G : ℂ → ℂ} {z w : ℂ} (hF : RectIntegrable F z w) (hG : RectIntegrable G z w) :
    rectInt (fun s => F s + G s) z w = rectInt F z w + rectInt G z w :=
  rectInt_add_of_integrable hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hG.1 hG.2.1 hG.2.2.1 hG.2.2.2

theorem rectInt_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (hF : ∀ i ∈ S, RectIntegrable (F i) z w) :
    rectInt (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectInt (F i) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectInt]
  | insert a S ha ih =>
    have hS : RectIntegrable (fun s => ∑ i ∈ S, F i s) z w := by
      have key : ∀ (φ : ℝ → ℂ) (a b : ℝ),
          (∀ i ∈ S, IntervalIntegrable (fun t => F i (φ t)) volume a b) →
          IntervalIntegrable (fun t => ∑ i ∈ S, F i (φ t)) volume a b := by
        intro φ a b h
        have := IntervalIntegrable.sum S h
        convert this using 1
        ext t; simp [Finset.sum_apply]
      exact ⟨key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).1,
        key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.1,
        key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.2.1,
        key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.2.2⟩
    simp only [Finset.sum_insert ha]
    rw [rectInt_add' (hF a (Finset.mem_insert_self a S)) hS,
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/-- The closed rectangle is the union of its interior and its four sides. -/
theorem mem_rect_cases {z w u : ℂ} (hu : u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) (hzw1 : z.re < w.re)
    (hzw2 : z.im < w.im) :
    (z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) ∨ u.im = z.im ∨ u.im = w.im ∨
      u.re = w.re ∨ u.re = z.re := by
  rw [mem_reProdIm, Set.uIcc_of_le hzw1.le, Set.uIcc_of_le hzw2.le] at hu
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hu
  rcases a1.lt_or_eq with a1 | a1
  · rcases a2.lt_or_eq with a2 | a2
    · rcases b1.lt_or_eq with b1 | b1
      · rcases b2.lt_or_eq with b2 | b2
        · exact Or.inl ⟨a1, a2, b1, b2⟩
        · exact Or.inr (Or.inr (Or.inl b2))
      · exact Or.inr (Or.inl b1.symm)
    · exact Or.inr (Or.inr (Or.inr (Or.inl a2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr a1.symm)))

/-- `F` has no zeros on the four sides. -/
def NoZerosOnSides (F : ℂ → ℂ) (z w : ℂ) : Prop :=
  (∀ x ∈ [[z.re, w.re]], F (x + z.im * I) ≠ 0) ∧ (∀ x ∈ [[z.re, w.re]], F (x + w.im * I) ≠ 0) ∧
  (∀ y ∈ [[z.im, w.im]], F (w.re + y * I) ≠ 0) ∧ (∀ y ∈ [[z.im, w.im]], F (z.re + y * I) ≠ 0)

theorem rectIntegrable_mul_inv_sub {h : ℂ → ℂ} {z w u : ℂ}
    (hh : ContinuousOn h ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hu1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) (hu2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u)
    (hu3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) (hu4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) :
    RectIntegrable (fun s => h s * (s - u)⁻¹) z w := by
  have hs := rect_sides_integrable hh
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun x hx => sub_ne_zero.2 (hu1 x hx))
    exact hh.comp (by fun_prop) fun x hx => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨hx, left_mem_uIcc⟩
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun x hx => sub_ne_zero.2 (hu2 x hx))
    exact hh.comp (by fun_prop) fun x hx => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨hx, right_mem_uIcc⟩
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun y hy => sub_ne_zero.2 (hu3 y hy))
    exact hh.comp (by fun_prop) fun y hy => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨right_mem_uIcc, hy⟩
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun y hy => sub_ne_zero.2 (hu4 y hy))
    exact hh.comp (by fun_prop) fun y hy => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨left_mem_uIcc, hy⟩

/-- **Residue theorem for `f'/f · h`** on a rectangle inside `ball c (R/2)`, `f` entire with no zeros
on the sides, `h` holomorphic near the closed rectangle:
`∮ (f'/f) h = 2πi Σ_{zeros ρ strictly inside} m_ρ h(ρ)`. -/
theorem rectInt_logDeriv_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : f c ≠ 0) {z w : ℂ} (hzw1 : z.re < w.re) (hzw2 : z.im < w.im)
    (hrect : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball c (R / 2)) (hbd : NoZerosOnSides f z w)
    {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hsubU : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U)
    (hh : DifferentiableOn ℂ h U) :
    rectInt (fun s => logDeriv f s * h s) z w = 2 * π * I *
      ∑ u ∈ (zerosIn f c R (R / 2)).filter
        (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
        ((divB f c R u).toNat : ℂ) * h u := by
  classical
  obtain ⟨g, hg, hg0, hfg⟩ := factor_ball hf hfc hR
  set Z := zerosIn f c R (R / 2) with hZ
  set Rect := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hRect
  have hRb : Rect ⊆ ball c R := hrect.trans (ball_subset_ball (by linarith))
  -- zeros of `f` in `Z` are zeros
  have hfu : ∀ u ∈ Z, f u = 0 := by
    intro u hu
    have hu' := (mem_zerosIn hu).2
    have hucR : u ∈ closedBall c R := by
      rw [mem_closedBall, dist_eq_norm]; linarith [(mem_zerosIn hu).1]
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (closedBall c R)) hucR] at hu'
    by_contra hne
    exact hu' (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
  -- pointwise decomposition of `f'/f` on the rectangle, away from zeros
  have hdec : ∀ s ∈ Rect, f s ≠ 0 →
      logDeriv f s = ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) / (s - u) + logDeriv g s := by
    intro s hs hfs
    have hsZ : ∀ u ∈ Z, s ≠ u := fun u hu h => hfs (h ▸ hfu u hu)
    have hsb : s ∈ ball c R := hRb hs
    have hsb2 : s ∈ ball c (R / 2) := hrect hs
    have hPs : Pin f c R s ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hsZ u hu))
    have hgs : g s ≠ 0 := hg0 s hsb2
    have hloc : f =ᶠ[nhds s] fun w => Pin f c R w * g w := by
      filter_upwards [isOpen_ball.mem_nhds hsb] with v hv
      exact hfg v (ball_subset_closedBall hv)
    have hPd : DifferentiableAt ℂ (Pin f c R) s := by
      have : Pin f c R = fun w => ∏ u ∈ Z, (w - u) ^ (divB f c R u).toNat := rfl
      rw [this]
      exact DifferentiableAt.fun_finsetProd fun u _ => (differentiableAt_id.sub_const u).pow _
    have hgd : DifferentiableAt ℂ g s := (hg s (ball_subset_closedBall hsb)).differentiableAt
    rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
      show (fun w => Pin f c R w * g w) = Pin f c R * g from rfl,
      logDeriv_mul (f := Pin f c R) (g := g) s hPs hgs hPd hgd, logDeriv_Pin hsZ]
  have hside1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ∈ Rect := fun x hx =>
    mem_reProdIm.2 ⟨by simpa using hx, by simp [left_mem_uIcc]⟩
  have hside2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ∈ Rect := fun x hx =>
    mem_reProdIm.2 ⟨by simpa using hx, by simp [right_mem_uIcc]⟩
  have hside3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ∈ Rect := fun y hy =>
    mem_reProdIm.2 ⟨by simp [right_mem_uIcc], by simpa using hy⟩
  have hside4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ∈ Rect := fun y hy =>
    mem_reProdIm.2 ⟨by simp [left_mem_uIcc], by simpa using hy⟩
  set F : ℂ → ℂ := fun s => (∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h s * (s - u)⁻¹)) +
    logDeriv g s * h s with hF
  have hpt : ∀ s ∈ Rect, f s ≠ 0 → logDeriv f s * h s = F s := by
    intro s hs hfs
    rw [hdec s hs hfs, add_mul, Finset.sum_mul, hF]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [div_eq_mul_inv]; ring
  obtain ⟨b1, b2, b3, b4⟩ := hbd
  rw [rectInt_congr' (g := F) (fun x hx => hpt _ (hside1 x hx) (b1 x hx))
    (fun x hx => hpt _ (hside2 x hx) (b2 x hx)) (fun y hy => hpt _ (hside3 y hy) (b3 y hy))
    (fun y hy => hpt _ (hside4 y hy) (b4 y hy))]
  have hhc : ContinuousOn h Rect := hh.continuousOn.mono hsubU
  -- `u ∈ Z` is not on the sides
  have hnot : ∀ u ∈ Z, (∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) ∧
      (∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u) ∧
      (∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) ∧ (∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) := by
    intro u hu
    refine ⟨fun x hx h' => b1 x hx (h' ▸ hfu u hu), fun x hx h' => b2 x hx (h' ▸ hfu u hu),
      fun y hy h' => b3 y hy (h' ▸ hfu u hu), fun y hy h' => b4 y hy (h' ▸ hfu u hu)⟩
  have hint_u : ∀ u ∈ Z, RectIntegrable (fun s => h s * (s - u)⁻¹) z w := fun u hu =>
    rectIntegrable_mul_inv_sub hhc (hnot u hu).1 (hnot u hu).2.1 (hnot u hu).2.2.1 (hnot u hu).2.2.2
  -- `g'/g · h` is holomorphic on the rectangle
  have hgdiff : DifferentiableOn ℂ (fun s => logDeriv g s * h s) Rect := by
    intro s hs
    have hga : AnalyticAt ℂ g s := hg s (ball_subset_closedBall (hRb hs))
    have hgs : g s ≠ 0 := hg0 s (hrect hs)
    have hhs : DifferentiableAt ℂ h s := hh.differentiableAt (hU.mem_nhds (hsubU hs))
    have : DifferentiableAt ℂ (logDeriv g) s := by
      have e : logDeriv g = fun s => deriv g s / g s := rfl
      rw [e]; exact hga.deriv.differentiableAt.div hga.differentiableAt hgs
    exact (this.mul hhs).differentiableWithinAt
  have hint_g : RectIntegrable (fun s => logDeriv g s * h s) z w :=
    rectIntegrable_of_continuousOn hgdiff.continuousOn
  have hint_sum : RectIntegrable (fun s => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h s * (s - u)⁻¹)) z w := by
    have key : ∀ (φ : ℝ → ℂ) (a b : ℝ),
        (∀ u ∈ Z, IntervalIntegrable (fun t => h (φ t) * (φ t - u)⁻¹) volume a b) →
        IntervalIntegrable (fun t => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h (φ t) * (φ t - u)⁻¹))
          volume a b := by
      intro φ a b hφ
      have := IntervalIntegrable.sum Z fun u hu => (hφ u hu).const_mul ((divB f c R u).toNat : ℂ)
      convert this using 1
      ext t; simp [Finset.sum_apply]
    exact ⟨key _ _ _ fun u hu => (hint_u u hu).1, key _ _ _ fun u hu => (hint_u u hu).2.1,
      key _ _ _ fun u hu => (hint_u u hu).2.2.1, key _ _ _ fun u hu => (hint_u u hu).2.2.2⟩
  have hg0' : rectInt (fun s => logDeriv g s * h s) z w = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w hgdiff
  rw [hF, rectInt_add' hint_sum hint_g, hg0', add_zero,
    rectInt_finset_sum Z _ fun u hu => (hint_u u hu).const_mul _]
  simp only [rectInt_const_mul]
  -- each term
  have hterm : ∀ u ∈ Z, ((divB f c R u).toNat : ℂ) * rectInt (fun s => h s * (s - u)⁻¹) z w =
      if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
        2 * π * I * (((divB f c R u).toNat : ℂ) * h u) else 0 := by
    intro u hu
    split_ifs with hin
    · rw [rectInt_mul_inv_sub hU hsubU hh hin.1 hin.2.1 hin.2.2.1 hin.2.2.2]; ring
    · by_cases huR : u ∈ Rect
      · exfalso
        rcases mem_rect_cases huR hzw1 hzw2 with h' | h' | h' | h' | h'
        · exact hin h'
        · exact (hnot u hu).1 u.re (by
            rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.1 u.re (by
            rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.2.1 u.im (by
            rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.2.2 u.im (by
            rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
      · have hd : DifferentiableOn ℂ (fun s => h s * (s - u)⁻¹) Rect := by
          intro s hs
          have hsu : s - u ≠ 0 := sub_ne_zero.2 (fun h' => huR (h' ▸ hs))
          exact ((hh.differentiableAt (hU.mem_nhds (hsubU hs))).mul
            ((differentiableAt_id.sub_const u).inv hsu)).differentiableWithinAt
        have h0 : rectInt (fun s => h s * (s - u)⁻¹) z w = 0 :=
          Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w hd
        rw [h0, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.mul_sum]

end TernaryGoldbach.Explicit
