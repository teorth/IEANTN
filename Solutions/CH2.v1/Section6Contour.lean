/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section8
import Section6Weight

/-!
# Section 6: the contour integral in `shiftError`

`shiftError` contains `‖∫_C Φ⋆(sgn λ · z(s)) F(s) x^s ds‖` over `LadderParams.intC`. With `δ = 1`
this contour and `coronidis`'s — `1 → -1 → -1 + i → -∞ + i` — bound a rectangle `[-1,1] × [0,1]`
in which the integrand is holomorphic, so the two integrals agree, and `coronidis` bounds them
with `Φ(s) = T Φ⋆(sgn λ · z(s))`.

`coronidis` asks for `‖Φ(s)‖ ≤ ‖s - 1‖` on the strip `Re s ≤ -1, |Im s| ≤ 1`; what is available
is `1.85 ‖s - 1‖` there (`norm_B_sub_le_strip`) and the sharp constant `1` on the real axis
(`norm_B_sub_le_real`). `coronidis185` is `coronidis` with that split: the constant `1.85` enters
only through the two `cot` legs, whose `9.42/x` has room up to `18/x`.
-/

open Complex Filter Topology CH2Section8

namespace CH2Section6

/-! ### `coronidis` with constant `1.85` off the real axis -/

theorem intV_div (Φ : ℂ → ℂ) (x : ℝ) (c : ℂ) : intV (fun s ↦ Φ s / c) x = intV Φ x / c := by
  unfold intV
  rw [← intervalIntegral.integral_div]
  congr 1; funext v; ring

theorem intH_div (Φ : ℂ → ℂ) (x : ℝ) (c : ℂ) : intH (fun s ↦ Φ s / c) x = intH Φ x / c := by
  unfold intH
  rw [← MeasureTheory.integral_div]
  congr 1; funext v; ring

theorem intClt_div (Φ : ℂ → ℂ) (x : ℝ) (c : ℂ) : intClt (fun s ↦ Φ s / c) x = intClt Φ x / c := by
  unfold intClt
  rw [add_div, ← intervalIntegral.integral_div, ← MeasureTheory.integral_div]
  congr 1
  · congr 1; funext v; ring
  · congr 1; funext v; ring

theorem intHoriz_div (Φ : ℂ → ℂ) (x : ℝ) (c : ℂ) :
    intHoriz (fun t : ℝ ↦ Φ ((1 - t : ℝ) : ℂ) / c) x
      = intHoriz (fun t : ℝ ↦ Φ ((1 - t : ℝ) : ℂ)) x / c := by
  unfold intHoriz
  rw [← MeasureTheory.integral_div]
  congr 1; funext v; ring

/-- **`prop:coronidis` with the strip constant `1.85`.** The sharp constant stays where the leading
term comes from: the segment `[-1, 1]` and the real half-line. -/
theorem coronidis185 (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hgam : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ {s : ℂ | s.re < 0})
    (hΦseg : ∀ t ∈ Set.Icc (0:ℝ) 2, ‖Φ ((1 - t : ℝ) : ℂ)‖ ≤ t)
    (hΦreal : ∀ u : ℝ, 0 < u → ‖Φ ((-1 - u : ℝ) : ℂ)‖ ≤ 2 + u)
    (hΦb : ∀ s : ℂ, s.re ≤ -1 → |s.im| ≤ 1 → ‖Φ s‖ ≤ 1.85 * ‖s - 1‖)
    {x : ℝ} (hx : 1000000 ≤ x) :
    ‖intSeg Φ x + intClt Φ x‖
      ≤ Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3 := by
  have hx15 : (15 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hc : (1.85 : ℂ) ≠ 0 := by norm_num
  have hcn : ‖(1.85 : ℂ)‖ = 1.85 := by
    rw [show (1.85 : ℂ) = ((1.85 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real]; norm_num
  set Φ' : ℂ → ℂ := fun s ↦ Φ s / 1.85 with hΦ'
  have hΦ'b : ∀ s : ℂ, s.re ≤ -1 → |s.im| ≤ 1 → ‖Φ' s‖ ≤ ‖s - 1‖ := by
    intro s h1 h2
    rw [hΦ', norm_div, hcn, div_le_iff₀ (by norm_num)]
    linarith [hΦb s h1 h2]
  have hΦ'd : DifferentiableOn ℂ Φ' {s : ℂ | s.re < 0} := hΦd.div_const _
  have hΦV : ∀ v ∈ Set.Icc (0:ℝ) 1, ‖Φ' (segV v)‖ ≤ ‖segV v - 1‖ := by
    intro v hv
    refine hΦ'b _ (by rw [segV_re]) ?_
    rw [segV_im, abs_of_nonneg hv.1]
    exact hv.2
  have hΦH : ∀ u ∈ Set.Ioi (0:ℝ), ‖Φ' (segH u)‖ ≤ ‖segH u - 1‖ := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    exact hΦ'b _ (by rw [segH_re]; linarith) (by rw [segH_im]; norm_num)
  have hΨ : ∀ u ∈ Set.Ioi (0:ℝ), ‖Φ ((1 - (2 + u) : ℝ) : ℂ)‖ ≤ 2 + u := by
    intro u hu
    have hs : ((1 - (2 + u) : ℝ) : ℂ) = ((-1 - u : ℝ) : ℂ) := by push_cast; ring
    rw [hs]
    exact hΦreal u hu
  -- `intClt_eq` for `Φ'`, scaled back
  have heq := intClt_eq hfe hgam h2v hΦ'd hΦH hΦ'b hx15
  rw [intClt_div, intV_div, intH_div,
    show (fun t : ℝ ↦ Φ' ((1 - t : ℝ) : ℂ)) = (fun t : ℝ ↦ Φ ((1 - t : ℝ) : ℂ) / 1.85) from rfl,
    intHoriz_div] at heq
  have heq' : intClt Φ x = -(intV Φ x + intH Φ x) + intHoriz (fun t : ℝ ↦ Φ ((1 - t : ℝ) : ℂ)) x := by
    have := congrArg (· * (1.85 : ℂ)) heq
    field_simp at this
    linear_combination this
  -- the two `cot` legs, with the constant
  have hVH : ‖intV Φ x + intH Φ x‖ ≤ 18 / x := by
    have hL : (2 : ℝ) < Real.log x := by
      have h1 : Real.log 15 ≤ Real.log x := Real.log_le_log (by norm_num) hx15
      have h2' : (2 : ℝ) < Real.log 15 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have h := Real.exp_one_lt_d9
        have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [he]
        nlinarith [Real.exp_pos 1]
      linarith
    have hA := norm_intV_le hΦV (by linarith : (1:ℝ) < x)
    have hB := norm_intH_le hΦH hx15
    have hC : (7.72 : ℝ) / (x * (Real.log x - 1 / 3)) ≤ 4.7 / x := by
      rw [div_le_div_iff₀ (by nlinarith) hx0]
      nlinarith
    rw [hΦ', intV_div, norm_div, hcn] at hA
    rw [hΦ', intH_div, norm_div, hcn] at hB
    have e : intV Φ x + intH Φ x = (1.85 : ℂ) * (intV Φ x / 1.85 + intH Φ x / 1.85) := by
      field_simp
    rw [e, norm_mul, hcn]
    have h3 := norm_add_le (intV Φ x / 1.85) (intH Φ x / 1.85)
    rw [norm_div, norm_div, hcn] at h3
    have h4 : (1.85 : ℝ) * (4.72 / x + 4.7 / x) ≤ 18 / x := by
      rw [show (1.85 : ℝ) * (4.72 / x + 4.7 / x) = 17.427 / x by field_simp; ring]
      exact div_le_div_of_nonneg_right (by norm_num) hx0.le
    calc (1.85 : ℝ) * ‖intV Φ x / 1.85 + intH Φ x / 1.85‖
        ≤ 1.85 * (4.72 / x + 4.7 / x) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith
      _ ≤ 18 / x := h4
  rw [heq']
  have htri : ‖intSeg Φ x + (-(intV Φ x + intH Φ x)
        + intHoriz (fun t : ℝ ↦ Φ ((1 - t : ℝ) : ℂ)) x)‖
      ≤ ‖intSeg Φ x‖ + ‖intV Φ x + intH Φ x‖
        + ‖intHoriz (fun t : ℝ ↦ Φ ((1 - t : ℝ) : ℂ)) x‖ := by
    refine le_trans (norm_add_le _ _) ?_
    have h := norm_add_le (-(intV Φ x + intH Φ x))
      (intHoriz (fun t : ℝ ↦ Φ ((1 - t : ℝ) : ℂ)) x)
    rw [norm_neg] at h
    linarith
  exact le_trans htri (coronidis_bound hk hneg h2v hΦseg hΨ hx hVH)

end CH2Section6
