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

/-! ### The weight `Φ(s) = T Φ⋆(sgn λ · z(s))` -/

/-- `Φ(s) = T Φ⋆(sgn λ · z(s))`, the `Φ` that `coronidis` is applied to. -/
noncomputable def PhiT (l : CH2.LadderParams) (lam ε : ℝ) (s : ℂ) : ℂ :=
  (l.T : ℂ) * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)

theorem PhiT_eq (l : CH2.LadderParams) {lam : ℝ} (ε : ℝ) (hlam : lam < 0) (s : ℂ) :
    PhiT l lam ε s = (l.T : ℂ) * (CH2.B ε (2 * Real.pi * (s - 1) / l.T + (|lam| : ℝ))
      - CH2.B ε ((|lam| : ℝ) : ℂ)) / (2 * Real.pi * I) := by
  have hTc : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr l.hT.ne'
  simp only [PhiT, CH2.Phi_star]
  rw [CH2.sign_cast_neg_one hlam]
  have e : -2 * (Real.pi : ℂ) * I * (-1 * l.zOf s) + ((|lam| : ℝ) : ℂ)
      = 2 * Real.pi * (s - 1) / l.T + (|lam| : ℝ) := by
    rw [CH2.LadderParams.zOf]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring
  rw [e]
  ring

theorem norm_PhiT (l : CH2.LadderParams) {lam : ℝ} (ε : ℝ) (hlam : lam < 0) (s : ℂ) :
    ‖PhiT l lam ε s‖ = l.T / (2 * Real.pi) *
      ‖CH2.B ε (2 * Real.pi * (s - 1) / l.T + (|lam| : ℝ)) - CH2.B ε ((|lam| : ℝ) : ℂ)‖ := by
  rw [PhiT_eq l ε hlam, mul_div_assoc, norm_mul, norm_div, Complex.norm_real, norm_mul, norm_mul,
    Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos l.hT, abs_of_pos Real.pi_pos]
  ring

theorem norm_PhiT_real_le (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam < 0) (hε : |ε| ≤ 1)
    (r : ℝ) : ‖PhiT l lam ε (r : ℂ)‖ ≤ |r - 1| := by
  have hT := l.hT
  have hπ := Real.pi_pos
  rw [norm_PhiT l ε hlam]
  have e : 2 * (Real.pi : ℂ) * ((r : ℂ) - 1) / l.T + ((|lam| : ℝ) : ℂ)
      = ((2 * Real.pi * (r - 1) / l.T + |lam| : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  have h := norm_B_sub_le_real hε (2 * Real.pi * (r - 1) / l.T + |lam|) |lam|
  have e2 : ‖((2 * Real.pi * (r - 1) / l.T + |lam| : ℝ) : ℂ) - ((|lam| : ℝ) : ℂ)‖
      = 2 * Real.pi / l.T * |r - 1| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show 2 * Real.pi * (r - 1) / l.T + |lam| - |lam| = 2 * Real.pi / l.T * (r - 1) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / l.T)]
  rw [e2] at h
  calc l.T / (2 * Real.pi) * _ ≤ l.T / (2 * Real.pi) * (2 * Real.pi / l.T * |r - 1|) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = |r - 1| := by field_simp

theorem norm_PhiT_strip_le (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam < 0) (hε : |ε| ≤ 1)
    (hT4 : 4 ≤ l.T) {s : ℂ} (hs : |s.im| ≤ 1) : ‖PhiT l lam ε s‖ ≤ 1.85 * ‖s - 1‖ := by
  have hT := l.hT
  have hπ := Real.pi_pos
  rw [norm_PhiT l ε hlam]
  have him : |(2 * (Real.pi : ℂ) * (s - 1) / l.T + ((|lam| : ℝ) : ℂ)).im| ≤ Real.pi / 2 := by
    have e : (2 * (Real.pi : ℂ) * (s - 1) / l.T + ((|lam| : ℝ) : ℂ)).im
        = 2 * Real.pi / l.T * s.im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero, Complex.div_ofReal_im]
      simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / l.T)]
    calc 2 * Real.pi / l.T * |s.im| ≤ 2 * Real.pi / l.T * 1 := by gcongr
      _ ≤ Real.pi / 2 := by
        rw [mul_one, div_le_div_iff₀ hT (by norm_num)]; nlinarith
  have h := norm_B_sub_le_strip (W' := ((|lam| : ℝ) : ℂ)) hε him (by simp; positivity)
  have e2 : ‖2 * (Real.pi : ℂ) * (s - 1) / l.T + ((|lam| : ℝ) : ℂ) - ((|lam| : ℝ) : ℂ)‖
      = 2 * Real.pi / l.T * ‖s - 1‖ := by
    rw [add_sub_cancel_right, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT, abs_of_pos hπ]
    ring
  rw [e2] at h
  calc l.T / (2 * Real.pi) * _ ≤ l.T / (2 * Real.pi) * (1.85 * (2 * Real.pi / l.T * ‖s - 1‖)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1.85 * ‖s - 1‖ := by field_simp

theorem differentiableOn_PhiT (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam < 0)
    (hσ0 : 0 ≤ l.sigmaOf lam) : DifferentiableOn ℂ (PhiT l lam ε) {s : ℂ | s.re < 0} := by
  intro s hs
  have hs' : s.re < 0 := hs
  have hav : l.AvoidsWeightPoles lam s := l.avoidsWeightPoles_of_re_ne (by linarith)
  exact ((l.analyticAt_Phi_star_neg hlam hav).differentiableAt.const_mul _).differentiableWithinAt

/-- **`coronidis` at `Φ = T Φ⋆(sgn λ · z(s))`.** -/
theorem coronidis_PhiT (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hgam : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam < 0) (hε : |ε| ≤ 1) (hT4 : 4 ≤ l.T)
    (hσ0 : 0 ≤ l.sigmaOf lam) {x : ℝ} (hx : 1000000 ≤ x) :
    ‖intSeg (PhiT l lam ε) x + intClt (PhiT l lam ε) x‖
      ≤ Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3 := by
  refine coronidis185 hfe hgam hk hneg h2v (differentiableOn_PhiT l hlam hσ0) ?_ ?_ ?_ hx
  · intro t ht
    refine (norm_PhiT_real_le l hlam hε _).trans (le_of_eq ?_)
    rw [show 1 - t - 1 = -t by ring, abs_neg, abs_of_nonneg ht.1]
  · intro u hu
    refine (norm_PhiT_real_le l hlam hε _).trans (le_of_eq ?_)
    rw [show -1 - u - 1 = -(2 + u) by ring, abs_neg, abs_of_pos (by linarith)]
  · intro s _ hs
    exact norm_PhiT_strip_le l hlam hε hT4 hs

end CH2Section6
