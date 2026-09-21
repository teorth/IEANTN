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

/-! ### The rectangle between the two contours -/

theorem integral_Ioi_neg_one_sub (k : ℝ → ℂ) :
    ∫ u in Set.Ioi (0:ℝ), k (-1 - u) = ∫ r in Set.Iic (-1:ℝ), k r := by
  have hmp := MeasureTheory.volume.measurePreserving_sub_left (G := ℝ) (-1)
  have hemb : MeasurableEmbedding (fun h : ℝ ↦ -1 - h) :=
    (Homeomorph.subLeft (-1 : ℝ)).isClosedEmbedding.measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb k (Set.Iic (-1))
  have hpre : (fun h : ℝ ↦ -1 - h) ⁻¹' Set.Iic (-1) = Set.Ici 0 := by
    ext u; simp
  rw [hpre, MeasureTheory.integral_Ici_eq_integral_Ioi] at h
  exact h

theorem integrableOn_Iic_of_Ioi {k : ℝ → ℂ}
    (h : MeasureTheory.IntegrableOn (fun u ↦ k (-1 - u)) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn k (Set.Iic (-1)) := by
  have hmp := MeasureTheory.volume.measurePreserving_sub_left (G := ℝ) (-1)
  have hemb : MeasurableEmbedding (fun h : ℝ ↦ -1 - h) :=
    (Homeomorph.subLeft (-1 : ℝ)).isClosedEmbedding.measurableEmbedding
  have e := hmp.integrableOn_comp_preimage hemb (f := k) (s := Set.Iic (-1))
  have hpre : (fun h : ℝ ↦ -1 - h) ⁻¹' Set.Iic (-1) = Set.Ici 0 := by
    ext u; simp
  rw [hpre, integrableOn_Ici_iff_integrableOn_Ioi] at e
  exact e.mp h

/-- `Ã = F` away from `1` and the zeros. -/
theorem Atilde_eq_F {z : ℂ} (hz1 : z ≠ 1) (hζ : riemannZeta z ≠ 0) :
    Atilde z = CH2ZetaInstance.F z := by
  rw [Atilde, CH2ZetaInstance.F, CH2ZetaInstance.logDeriv_riemannZeta₁_eq hz1 hζ, logDeriv_apply]
  ring

theorem riemannZeta_ne_zero_left {z : ℂ} (hre : z.re < 0) (him : z.im ≠ 0 ∨ -2 < z.re) :
    riemannZeta z ≠ 0 := by
  refine CH2ZetaInstance.riemannZeta_ne_zero_of_re_neg hre fun n hn ↦ ?_
  rw [hn] at him
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases him with h | h
  · simp at h
  · simp at h; linarith

/-- The zeros of `ζ` miss `[-1,1] × [-1,1]` once `R_C` (with `δ = 1`) holds only trivial ones. -/
theorem riemannZeta_ne_zero_box (l : CH2.LadderParams) (hδ1 : l.δ = 1)
    (hRC : ∀ z ∈ l.RC, riemannZeta z = 0 → z.re < 0) {z : ℂ} (hre : -1 ≤ z.re) (hre1 : z.re ≤ 1)
    (him : |z.im| ≤ 1) : riemannZeta z ≠ 0 := by
  intro h0
  have hneg := hRC z ⟨hre1, by rw [hδ1]; exact him⟩ h0
  exact riemannZeta_ne_zero_left hneg (Or.inr (by linarith)) h0

theorem analyticAt_PhiT (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam < 0) {z : ℂ}
    (hz : |z.im| < l.T) : AnalyticAt ℂ (PhiT l lam ε) z := by
  have hT := l.hT
  refine analyticAt_const.mul ((CH2.Phi_star.analyticAt_of_not_pole_nz |lam| ε _ ?_).comp_of_eq
    (l.analyticAt_zOf (Real.sign lam : ℂ) z) rfl)
  intro n hn heq
  have h2 : ((n : ℂ) - I * ((|lam| : ℝ) : ℂ) / (2 * (Real.pi : ℂ))).re = n := by
    rw [show I * ((|lam| : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) = ((|lam| / (2 * Real.pi) : ℝ) : ℂ) * I by
      push_cast; ring]
    simp [Complex.div_im]
  have hre := congrArg Complex.re heq
  rw [h2, CH2.sign_cast_neg_one hlam, neg_one_mul, Complex.neg_re, CH2ZetaInstance.re_zOf] at hre
  have h1 : |(n : ℝ)| < 1 := by
    rw [← hre, abs_neg, abs_div, abs_of_pos hT, div_lt_one hT]; exact hz
  have : n = 0 := by
    have h3 : |n| < 1 := by exact_mod_cast h1
    have := abs_lt.mp h3
    omega
  exact hn this

/-- The ray integrand is integrable, for any `Φ` with the `1.85` strip bound. -/
theorem integrableOn_Atilde_segH (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hgam : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ {s : ℂ | s.re < 0})
    (hΦb : ∀ s : ℂ, s.re ≤ -1 → |s.im| ≤ 1 → ‖Φ s‖ ≤ 1.85 * ‖s - 1‖)
    {x : ℝ} (hx : 15 ≤ x) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ -(Atilde (segH u) * Φ (segH u) * (x : ℂ) ^ segH u)) (Set.Ioi 0) := by
  have hcn : ‖(1.85 : ℂ)‖ = 1.85 := by
    rw [show (1.85 : ℂ) = ((1.85 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real]; norm_num
  set Φ' : ℂ → ℂ := fun s ↦ Φ s / 1.85 with hΦ'
  have hΦ'b : ∀ s : ℂ, s.re ≤ -1 → |s.im| ≤ 1 → ‖Φ' s‖ ≤ ‖s - 1‖ := by
    intro s h1 h2
    rw [hΦ', norm_div, hcn, div_le_iff₀ (by norm_num)]
    linarith [hΦb s h1 h2]
  have hΦ'd : DifferentiableOn ℂ Φ' {s : ℂ | s.re < 0} := hΦd.div_const _
  have hΦH : ∀ u ∈ Set.Ioi (0:ℝ), ‖Φ' (segH u)‖ ≤ ‖segH u - 1‖ := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    exact hΦ'b _ (by rw [segH_re]; linarith) (by rw [segH_im]; norm_num)
  have hJ := ((integrableOn_neg_Fint_segH hgam h2v hΦ'd hΦ'b hx).sub
    (integrableOn_cot_segH hΦ'd hΦH hx)).const_mul (1.85 : ℂ)
  refine MeasureTheory.IntegrableOn.congr_fun hJ (fun u hu ↦ ?_) measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := hu
  have hg := Gfun_eq hfe (by rw [segH_re]; linarith : (segH u).re < 0) (sin_pi_segH_ne_zero u)
  simp only [Fint, hg, hΦ', Pi.sub_apply]
  field_simp
  try ring

/-- **The rectangle identity.** With `δ = 1`, `T ∫_C Φ⋆ F x^s ds` is `coronidis`'s integral. -/
theorem intC_eq_coronidis (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hgam : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (l : CH2.LadderParams) (hδ1 : l.δ = 1) {lam ε : ℝ} (hlam : lam < 0) (hε : |ε| ≤ 1)
    (hT4 : 4 ≤ l.T) (hσ0 : 0 ≤ l.sigmaOf lam)
    (hRC : ∀ z ∈ l.RC, riemannZeta z = 0 → z.re < 0) {x : ℝ} (hx : 15 ≤ x) :
    (l.T : ℂ) * l.intC (fun s ↦ CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)
        * CH2ZetaInstance.F s * (x : ℂ) ^ s)
      = intSeg (PhiT l lam ε) x + intClt (PhiT l lam ε) x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hT := l.hT
  set G : ℂ → ℂ := fun s ↦ PhiT l lam ε s * CH2ZetaInstance.F s * (x : ℂ) ^ s with hG
  set k : ℝ → ℂ := fun r ↦ G ((r : ℂ) + I) with hk
  -- `G` is holomorphic on the closed rectangle
  have hGa : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 1 → |z.im| ≤ 1 → AnalyticAt ℂ G z := by
    intro z h1 h2 h3
    have hP := analyticAt_PhiT l (ε := ε) hlam (z := z) (by linarith)
    have hF : AnalyticAt ℂ CH2ZetaInstance.F z := by
      by_cases hz1 : z = 1
      · rw [hz1]; exact CH2ZetaInstance.analyticAt_F_one
      · exact CH2ZetaInstance.analyticAt_F_of_zeta_ne_zero hz1
          (riemannZeta_ne_zero_box l hδ1 hRC h1 h2 h3)
    exact (hP.mul hF).mul (CH2ZetaInstance.analyticAt_const_cpow hx0 z)
  have hGd : DifferentiableOn ℂ G (Set.uIcc (-1 : ℂ).re (1 + I).re ×ℂ Set.uIcc (-1 : ℂ).im (1 + I).im) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    simp only [Complex.neg_re, Complex.one_re, Complex.add_re, Complex.I_re, add_zero,
      Complex.neg_im, Complex.one_im, neg_zero, Complex.add_im, Complex.I_im, zero_add] at hz
    obtain ⟨hre, him⟩ := hz
    rw [Set.uIcc_of_le (by norm_num)] at hre him
    exact (hGa z hre.1 hre.2 (by rw [abs_of_nonneg him.1]; exact him.2)).differentiableAt.differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G (-1) (1 + I) hGd
  simp only [Complex.neg_re, Complex.one_re, Complex.add_re, Complex.I_re, add_zero,
    Complex.neg_im, Complex.one_im, neg_zero, Complex.add_im, Complex.I_im, zero_add, zero_mul,
    one_mul, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero] at hrect
  -- the `ζ ≠ 0` facts along the contours
  have hζV : ∀ v : ℝ, riemannZeta (segV v) ≠ 0 := fun v ↦
    riemannZeta_ne_zero_left (by rw [segV_re]; norm_num) (Or.inr (by rw [segV_re]; norm_num))
  have hV1 : ∀ v : ℝ, segV v ≠ 1 := by
    intro v h; have := congrArg Complex.re h; rw [segV_re] at this; norm_num at this
  have hζH : ∀ u : ℝ, riemannZeta (segH u) ≠ 0 := fun u ↦ by
    intro h0
    have him : (segH u).im ≠ 0 := by rw [segH_im]; norm_num
    have hs := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero h0 him
    have hRC' := hRC (segH u) ⟨hs.2, by rw [hδ1, segH_im]; norm_num⟩ h0
    exact riemannZeta_ne_zero_left hRC' (Or.inl him) h0
  -- (a) the left side
  have hVseg : (l.T : ℂ) * CH2.intVSeg 1 0 1 (fun s ↦ CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)
        * CH2ZetaInstance.F s * (x : ℂ) ^ s) = I * ∫ y in (0:ℝ)..1, G (1 + (y : ℂ) * I) := by
    unfold CH2.intVSeg
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1; funext y
    simp only [hG, PhiT, Complex.ofReal_one]
    ring
  have hkint : MeasureTheory.IntegrableOn k (Set.Iic 1) := by
    have h1 : MeasureTheory.IntegrableOn k (Set.Iic (-1)) := by
      refine integrableOn_Iic_of_Ioi ?_
      have hJ := (integrableOn_Atilde_segH hfe hgam h2v (differentiableOn_PhiT l hlam hσ0)
        (fun s _ hs ↦ norm_PhiT_strip_le l hlam hε hT4 hs) hx).neg
      refine MeasureTheory.IntegrableOn.congr_fun hJ (fun u hu ↦ ?_) measurableSet_Ioi
      have hu0 : (0 : ℝ) < u := hu
      have hs : segH u = (((-1 - u : ℝ) : ℂ)) + I := rfl
      simp only [Pi.neg_apply, neg_neg, hk, hG]
      rw [Atilde_eq_F (by intro h; have := congrArg Complex.im h; rw [segH_im] at this; norm_num at this)
        (hζH u), hs]
      ring
    have h2 : MeasureTheory.IntegrableOn k (Set.Icc (-1) 1) := by
      refine ContinuousOn.integrableOn_Icc fun r hr ↦ ?_
      refine ((hGa _ ?_ ?_ ?_).continuousAt.comp (by fun_prop : Continuous fun r : ℝ ↦ (r : ℂ) + I).continuousAt).continuousWithinAt
      · simp; exact hr.1
      · simp; exact hr.2
      · simp
    rw [← Set.Iic_union_Ioc_eq_Iic (by norm_num : (-1 : ℝ) ≤ 1)]
    exact h1.union (h2.mono_set Set.Ioc_subset_Icc_self)
  have hkint' : MeasureTheory.IntegrableOn k (Set.Iic (-1)) := hkint.mono_set (Set.Iic_subset_Iic.mpr (by norm_num))
  have hHray : (l.T : ℂ) * CH2.intHRay 1 1 (fun s ↦ CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)
        * CH2ZetaInstance.F s * (x : ℂ) ^ s)
      = (∫ r in Set.Iic (-1:ℝ), k r) + ∫ r in (-1:ℝ)..1, G ((r : ℂ) + I) := by
    unfold CH2.intHRay
    rw [← MeasureTheory.integral_const_mul]
    have e : (∫ r in Set.Iic (1:ℝ), (l.T : ℂ) * (CH2.Phi_star |lam| ε ((Real.sign lam : ℂ)
        * l.zOf (r + (1:ℝ) * I)) * CH2ZetaInstance.F (r + (1:ℝ) * I) * (x : ℂ) ^ (r + (1:ℝ) * I)))
        = ∫ r in Set.Iic (1:ℝ), k r := by
      congr 1; funext r
      simp only [hk, hG, PhiT, Complex.ofReal_one, one_mul]
      ring
    rw [e, ← intervalIntegral.integral_Iic_sub_Iic hkint' hkint]
    ring
  -- (b) the segment
  have hSeg : intSeg (PhiT l lam ε) x = -∫ r in (-1:ℝ)..1, G (r : ℂ) := by
    unfold intSeg
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_sub_left (fun r : ℝ ↦ Atilde (r : ℂ) * PhiT l lam ε (r : ℂ)
        * (x : ℂ) ^ (r : ℂ)) 1]
    norm_num
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ r : ℝ ∂MeasureTheory.volume, r ≠ 1 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with r hr1 hr
    rw [Set.uIoc_of_le (by norm_num)] at hr
    have hz1 : (r : ℂ) ≠ 1 := by exact_mod_cast hr1
    rw [Atilde_eq_F hz1 (riemannZeta_ne_zero_box l hδ1 hRC (by simp; linarith [hr.1])
      (by simp; exact hr.2) (by simp))]
    simp only [hG]
    ring
  -- (c) the two legs of `C_<`
  have hClt : intClt (PhiT l lam ε) x
      = I * (∫ y in (0:ℝ)..1, G (-1 + (y : ℂ) * I)) - ∫ r in Set.Iic (-1:ℝ), k r := by
    unfold intClt
    have e1 : (∫ v in (0:ℝ)..1, Atilde (segV v) * PhiT l lam ε (segV v) * (x : ℂ) ^ segV v * I)
        = I * ∫ y in (0:ℝ)..1, G (-1 + (y : ℂ) * I) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext v
      rw [Atilde_eq_F (hV1 v) (hζV v)]
      simp only [hG, segV]
      ring
    have e2 : (∫ u in Set.Ioi (0:ℝ), -(Atilde (segH u) * PhiT l lam ε (segH u) * (x : ℂ) ^ segH u))
        = -∫ r in Set.Iic (-1:ℝ), k r := by
      rw [← integral_Ioi_neg_one_sub, ← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
      have hs : segH u = (((-1 - u : ℝ) : ℂ)) + I := rfl
      rw [Atilde_eq_F (by intro h; have := congrArg Complex.im h; rw [segH_im] at this; norm_num at this)
        (hζH u)]
      simp only [hk, hG, hs]
      ring
    rw [e1, e2]
    ring
  rw [CH2.LadderParams.intC, hδ1, mul_sub, hVseg, hHray, hSeg, hClt]
  linear_combination hrect

/-- **The contour term of `shiftError`**: `‖∫_C Φ⋆ F x^s ds‖ ≤ (γ x/log² x + 1.8 x/log³ x)/T`. -/
theorem norm_intC_le (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hgam : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (l : CH2.LadderParams) (hδ1 : l.δ = 1) {lam ε : ℝ} (hlam : lam < 0) (hε : |ε| ≤ 1)
    (hT4 : 4 ≤ l.T) (hσ0 : 0 ≤ l.sigmaOf lam)
    (hRC : ∀ z ∈ l.RC, riemannZeta z = 0 → z.re < 0) {x : ℝ} (hx : 1000000 ≤ x) :
    ‖l.intC (fun s ↦ CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)
        * CH2ZetaInstance.F s * (x : ℂ) ^ s)‖
      ≤ (Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3) / l.T := by
  have hT := l.hT
  have h := intC_eq_coronidis hfe hgam h2v l hδ1 hlam hε hT4 hσ0 hRC (by linarith)
  have hb := coronidis_PhiT hfe hgam hk hneg h2v l hlam hε hT4 hσ0 hx
  rw [← h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT] at hb
  rw [le_div_iff₀ hT, mul_comm]
  exact hb

end CH2Section6
