/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Decay
import IEANTN.Nodes.CH2.v3.Conclusions

/-!
# Solution: `CH2.v3`

The bridge from the ported construction to the node's two existential statements.

Two things happen here that are not in the port. First, the node quantifies over a NON-ZERO
`lambda` where upstream builds everything for a positive parameter, so the negative case is
obtained by reflecting `ϕ_pm`. Second, the node pins `φ 0` as a complex number where upstream only
ever computes its real part.
-/

open Real MeasureTheory FourierTransform Complex

namespace CH2V3Sol

/-- Reflection. Carries upstream's positive parameter to the node's negative one. -/
noncomputable def refl' (φ : ℝ → ℂ) : ℝ → ℂ := fun t ↦ φ (-t)

lemma fourier_refl' (φ : ℝ → ℂ) (y : ℝ) : 𝓕 (refl' φ) y = 𝓕 φ (-y) := by
  simp only [Real.fourier_eq, refl']
  rw [← integral_neg_eq_self]
  simp

/-- `truncExp` at a positive parameter is the port's `Inu`. -/
lemma truncExp_pos {ν : ℝ} (hν : 0 < ν) (u : ℝ) : CH2.v2.truncExp ν u = CH2.Inu ν u := by
  unfold CH2.v2.truncExp CH2.Inu
  have h : (0 ≤ ν * u) ↔ (0 ≤ u) := by
    constructor
    · intro h; nlinarith
    · intro h; positivity
  simp only [h]

/-- `truncExp` at a negative parameter is the port's `Inu`, reflected. -/
lemma truncExp_neg {ν : ℝ} (hν : 0 < ν) (u : ℝ) : CH2.v2.truncExp (-ν) u = CH2.Inu ν (-u) := by
  unfold CH2.v2.truncExp CH2.Inu
  have h : (0 ≤ -ν * u) ↔ (0 ≤ -u) := by
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  simp only [h]
  by_cases hu : 0 ≤ -u
  · simp only [if_pos hu]; ring_nf
  · simp only [if_neg hu]

lemma phi_pm_zero_outside (ν ε : ℝ) {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) :
    CH2.ϕ_pm ν ε x = 0 := by
  unfold CH2.ϕ_pm
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hx ⟨h1, h2⟩

/-- The value at `0`, as a complex number rather than only its real part.

`Phi_circ ν ε z = ½(coth(w/2) + ε)` with `w = -2πIz + ν`, so at `z = 0` the argument is the real
number `ν` and the whole value is real. -/
lemma phi_pm_at_zero (ν ε : ℝ) : CH2.ϕ_pm ν ε 0 = (1 / 2) * (CH2.coth ((ν : ℂ) / 2) + ε) := by
  unfold CH2.ϕ_pm
  rw [if_pos (by norm_num)]
  simp only [Real.sign_zero, ofReal_zero, zero_mul, add_zero, CH2.Phi_circ]
  norm_num

lemma coth_ofReal (x : ℝ) : CH2.coth ((x : ℝ) : ℂ) = ((1 / Real.tanh x : ℝ) : ℂ) := by
  rw [CH2.coth, ← Complex.ofReal_tanh]
  push_cast
  rfl

lemma phi_pm_at_zero_plus {ν : ℝ} (hν : 0 < ν) :
    CH2.ϕ_pm ν 1 0 = ((1 / (1 - Real.exp (-ν)) : ℝ) : ℂ) := by
  have key : (1 / 2 : ℝ) * (1 / Real.tanh (ν / 2) + 1) = 1 / (1 - Real.exp (-ν)) := by
    obtain ⟨a, ha0, ha1, hexp, hb, ha2⟩ :
        ∃ a : ℝ, 0 < a ∧ 1 < a ∧ Real.exp (ν / 2) = a ∧ Real.exp (-(ν / 2)) = a⁻¹ ∧
          a ^ 2 = Real.exp ν := by
      refine ⟨Real.exp (ν / 2), Real.exp_pos _, ?_, rfl, by rw [Real.exp_neg], ?_⟩
      · rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
        exact Real.exp_lt_exp.mpr (by linarith)
      · rw [sq, ← Real.exp_add]; ring_nf
    have hinv : a⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; exact ha1
    have h1 : a - a⁻¹ ≠ 0 := sub_ne_zero.mpr (by linarith)
    have h2 : a + a⁻¹ ≠ 0 := by positivity
    have hnu : Real.exp (-ν) = (a ^ 2)⁻¹ := by rw [ha2, ← Real.exp_neg]
    have h3 : (1 : ℝ) - (a ^ 2)⁻¹ ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      have hlt : (a ^ 2)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; nlinarith
      intro hcon; rw [← hcon] at hlt; linarith
    have h4 : a ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (by nlinarith)
    have h5 : -1 + a ^ 2 ≠ 0 := by rw [show -1 + a ^ 2 = a ^ 2 - 1 by ring]; exact h4
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hexp, hb, hnu]
    field_simp
    ring
  rw [phi_pm_at_zero]
  have h2 : ((ν : ℂ) / 2) = (((ν / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [h2, coth_ofReal _, ← key]
  push_cast
  ring

lemma phi_pm_at_zero_minus {ν : ℝ} (hν : 0 < ν) :
    CH2.ϕ_pm ν (-1) 0 = ((1 / (Real.exp ν - 1) : ℝ) : ℂ) := by
  have key : (1 / 2 : ℝ) * (1 / Real.tanh (ν / 2) + (-1)) = 1 / (Real.exp ν - 1) := by
    obtain ⟨a, ha0, ha1, hexp, hb, ha2⟩ :
        ∃ a : ℝ, 0 < a ∧ 1 < a ∧ Real.exp (ν / 2) = a ∧ Real.exp (-(ν / 2)) = a⁻¹ ∧
          a ^ 2 = Real.exp ν := by
      refine ⟨Real.exp (ν / 2), Real.exp_pos _, ?_, rfl, by rw [Real.exp_neg], ?_⟩
      · rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
        exact Real.exp_lt_exp.mpr (by linarith)
      · rw [sq, ← Real.exp_add]; ring_nf
    have hinv : a⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; exact ha1
    have h1 : a - a⁻¹ ≠ 0 := sub_ne_zero.mpr (by linarith)
    have h2 : a + a⁻¹ ≠ 0 := by positivity
    have h3 : a ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (by nlinarith)
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hexp, hb, ← ha2]
    field_simp
    ring
  rw [phi_pm_at_zero]
  have h2 : ((ν : ℂ) / 2) = (((ν / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [h2, coth_ofReal _, ← key]
  push_cast
  ring

/-- Band-limitedness of the approximant, assembled from the port. -/
lemma bandLimited_phi (ν ε β : ℝ) (hν : 0 < ν) (hε : ε = 1 ∨ ε = -1)
    (hβ1 : 1 < β) (hβ2 : β ≤ 2) : CH2.v2.IsBandLimited (CH2.ϕ_pm ν ε) β := by
  obtain ⟨C, hC0, hC⟩ := CH2.varphi_fourier_bound ν ε hν hε
  refine ⟨(CH2.ϕ_continuous ν ε hν.ne').measurable, CH2.varphi_integ ν ε hν.ne',
    (CH2.ϕ_continuous ν ε hν.ne').continuousAt, fun x hx ↦ phi_pm_zero_outside ν ε hx, C, ?_⟩
  intro y hy
  have hy0 : (0 : ℝ) < |y| := abs_pos.mpr hy
  refine (hC y).trans ?_
  rcases le_or_gt 1 |y| with hbig | hsmall
  · have h1 : |y| ^ β ≤ |y| ^ (2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hbig hβ2
    have h2 : |y| ^ (2 : ℝ) = y ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hpow : (0 : ℝ) < |y| ^ β := Real.rpow_pos_of_pos hy0 β
    have hle : |y| ^ β ≤ 1 + y ^ 2 := by rw [h2] at h1; nlinarith [sq_nonneg y]
    gcongr <;> first | exact hC0 | exact hpow | exact hle | positivity | linarith
  · have h1 : |y| ^ β ≤ 1 := by
      calc |y| ^ β ≤ |y| ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_ge hy0 hsmall.le (by linarith)
        _ = 1 := Real.rpow_zero _
    have hpow : (0 : ℝ) < |y| ^ β := Real.rpow_pos_of_pos hy0 β
    have hle : |y| ^ β ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
    gcongr <;> first | exact hC0 | exact hpow | exact hle | positivity | linarith

lemma bandLimited_refl' (φ : ℝ → ℂ) (β : ℝ) (h : CH2.v2.IsBandLimited φ β) :
    CH2.v2.IsBandLimited (refl' φ) β := by
  obtain ⟨hm, hi, hc, hs, C, hC⟩ := h
  refine ⟨hm.comp measurable_neg, ?_, ?_, ?_, C, ?_⟩
  · exact hi.comp_neg
  · show ContinuousAt (fun t : ℝ ↦ φ (-t)) 0
    exact ContinuousAt.comp (by simpa using hc) continuous_neg.continuousAt
  · intro x hx
    refine hs (-x) ?_
    intro hcon
    exact hx ⟨by simpa using neg_le_neg hcon.2, by simpa using neg_le_neg hcon.1⟩
  · intro y hy
    rw [fourier_refl']
    simpa using hC (-y) (by simpa using hy)

end CH2V3Sol

open CH2V3Sol in
theorem CH2.v3.challenge_extremal_majorant : CH2.v3.extremal_majorant := by
  intro lambda β hlam hβ1 hβ2
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · -- `lambda < 0`: reflect the positive-parameter approximant.
    set ν : ℝ := -lambda with hνdef
    have hν : 0 < ν := by rw [hνdef]; linarith
    have habs : |lambda| = ν := by rw [hνdef, abs_of_neg hneg]
    refine ⟨refl' (CH2.ϕ_pm ν 1), bandLimited_refl' _ _ (bandLimited_phi ν 1 β hν (Or.inl rfl) hβ1 hβ2),
      ?_, ?_, ?_⟩
    · intro y
      rw [fourier_refl', show lambda = -ν by rw [hνdef]; ring, truncExp_neg hν]
      exact (CH2.Inu_bounds ν (-y) hν).2
    · rw [habs, refl', neg_zero]
      exact phi_pm_at_zero_plus hν
    · have hport := CH2.varphi_fourier_plus_error ν hν
      rw [MeasureTheory.setIntegral_univ] at hport
      rw [habs, ← hport]
      have : ∀ y : ℝ, (𝓕 (refl' (CH2.ϕ_pm ν 1)) y).re - CH2.v2.truncExp lambda y
          = (fun y : ℝ ↦ (𝓕 (CH2.ϕ_pm ν 1) y).re - CH2.Inu ν y) (-y) := by
        intro y
        rw [fourier_refl', show lambda = -ν by rw [hνdef]; ring, truncExp_neg hν]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall this)]
      exact integral_neg_eq_self (fun y : ℝ ↦ (𝓕 (CH2.ϕ_pm ν 1) y).re - CH2.Inu ν y) volume
  · -- `lambda > 0`: upstream's approximant directly.
    refine ⟨CH2.ϕ_pm lambda 1, bandLimited_phi lambda 1 β hpos (Or.inl rfl) hβ1 hβ2, ?_, ?_, ?_⟩
    · intro y
      rw [truncExp_pos hpos]
      exact (CH2.Inu_bounds lambda y hpos).2
    · rw [abs_of_pos hpos]
      exact phi_pm_at_zero_plus hpos
    · have hport := CH2.varphi_fourier_plus_error lambda hpos
      rw [MeasureTheory.setIntegral_univ] at hport
      rw [abs_of_pos hpos, ← hport]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y ↦ by simp only [truncExp_pos hpos])

open CH2V3Sol in
theorem CH2.v3.challenge_extremal_minorant : CH2.v3.extremal_minorant := by
  intro lambda β hlam hβ1 hβ2
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · set ν : ℝ := -lambda with hνdef
    have hν : 0 < ν := by rw [hνdef]; linarith
    have habs : |lambda| = ν := by rw [hνdef, abs_of_neg hneg]
    refine ⟨refl' (CH2.ϕ_pm ν (-1)),
      bandLimited_refl' _ _ (bandLimited_phi ν (-1) β hν (Or.inr rfl) hβ1 hβ2), ?_, ?_, ?_⟩
    · intro y
      rw [fourier_refl', show lambda = -ν by rw [hνdef]; ring, truncExp_neg hν]
      exact (CH2.Inu_bounds ν (-y) hν).1
    · rw [habs, refl', neg_zero]
      exact phi_pm_at_zero_minus hν
    · have hport := CH2.varphi_fourier_minus_error ν hν
      rw [MeasureTheory.setIntegral_univ] at hport
      rw [habs, ← hport]
      have : ∀ y : ℝ, CH2.v2.truncExp lambda y - (𝓕 (refl' (CH2.ϕ_pm ν (-1))) y).re
          = (fun y : ℝ ↦ CH2.Inu ν y - (𝓕 (CH2.ϕ_pm ν (-1)) y).re) (-y) := by
        intro y
        rw [fourier_refl', show lambda = -ν by rw [hνdef]; ring, truncExp_neg hν]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall this)]
      exact integral_neg_eq_self (fun y : ℝ ↦ CH2.Inu ν y - (𝓕 (CH2.ϕ_pm ν (-1)) y).re) volume
  · refine ⟨CH2.ϕ_pm lambda (-1),
      bandLimited_phi lambda (-1) β hpos (Or.inr rfl) hβ1 hβ2, ?_, ?_, ?_⟩
    · intro y
      rw [truncExp_pos hpos]
      exact (CH2.Inu_bounds lambda y hpos).1
    · rw [abs_of_pos hpos]
      exact phi_pm_at_zero_minus hpos
    · have hport := CH2.varphi_fourier_minus_error lambda hpos
      rw [MeasureTheory.setIntegral_univ] at hport
      rw [abs_of_pos hpos, ← hport]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y ↦ by simp only [truncExp_pos hpos])
