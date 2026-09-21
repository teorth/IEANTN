/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section81Hardin

/-!
# Section 9: `prop:sagaro` at the chosen height

`svm_abs_bound` (section 6) reduces `ψ_σ(x)/x^{1-σ} - Main` to two inputs: `Z`, a bound for the
`ω⁺` zero sum weighted by `x^{Re ρ}`, and `E`, a bound for `shiftError`. This file supplies both at
the height `t ∈ [T - 1/2, T]` produced by `lem:hardin`:

* `Z` is `prop:vihuela` times `√x` (under RH every zero has `Re ρ = 1/2`) times `t/2π`;
* `E` is `lem:hardin` (the two horizontal integrals) plus `norm_intC_le` (the contour term).

The result, `sagaro_at_t`, is `prop:sagaro` before the passage from `t` to `T`.
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section9

open CH2Section6 CH2Section81

/-- A ladder of height `t` with `δ = 1` and the `ζ` abscissas. -/
theorem exists_ladder {t : ℝ} (ht : 4 < t) :
    ∃ l : CH2.LadderParams, l.σ = CH2ZetaInstance.sigmaZeta ∧ l.T = t ∧ l.δ = 1 := by
  refine ⟨{ σ := CH2ZetaInstance.sigmaZeta, T := t, δ := 1, h0 := ?_, hσ := ?_, hlim := ?_, hδ := ?_ }, rfl, rfl, rfl⟩
  · simp [CH2ZetaInstance.sigmaZeta]
  · intro n
    simp only [CH2ZetaInstance.sigmaZeta]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · refine Filter.tendsto_atBot.2 (fun b ↦ ?_)
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil ((1 - b) / 2))] with n hn
    have h : ((1 - b) / 2 : ℝ) ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    simp only [CH2ZetaInstance.sigmaZeta]
    linarith
  · exact ⟨by norm_num, by linarith⟩

theorem RH_mono {t T : ℝ} (h : t ≤ T) (hRH : IEANTN.RiemannHypothesisUpTo T) :
    IEANTN.RiemannHypothesisUpTo t :=
  ⟨fun z ↦ hRH.false ⟨z.1, z.2.1, ⟨z.2.2.1.1, le_trans z.2.2.1.2 h⟩, z.2.2.2⟩⟩

/-- The two index sets agree: no zero has `Re ρ > 1`, and none has `0 < Im ρ ≤ 1`. -/
theorem zsum_Iic_Ioc_eq (hsmall : ZeroCount.v1.rvm_error_small) (f : ℂ → ℝ) {t : ℝ} :
    IEANTN.zetaZeroesSum (Set.Iic 1) (Set.Ioc 1 t) f
      = IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) f := by
  have hπ := Real.pi_gt_three
  have hset : IEANTN.zetaZeroesIn (Set.Iic 1) (Set.Ioc 1 t)
      = IEANTN.zetaZeroesIn Set.univ (Set.Ioc 0 t) := by
    ext ρ
    constructor
    · rintro ⟨-, ⟨h1, h2⟩, hz⟩
      exact ⟨trivial, ⟨by linarith, h2⟩, hz⟩
    · rintro ⟨-, ⟨h1, h2⟩, hz⟩
      refine ⟨?_, ⟨?_, h2⟩, hz⟩
      · exact (CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hz (by linarith)).2
      · by_contra hc
        push_neg at hc
        exact CH2Section6.no_zero_low hsmall hz h1 (by linarith)
  unfold IEANTN.zetaZeroesSum
  rw [tsum_subtype (IEANTN.zetaZeroesIn (Set.Iic 1) (Set.Ioc 1 t))
      (fun ρ ↦ f ρ * (IEANTN.zetaOrder ρ : ℝ)),
    tsum_subtype (IEANTN.zetaZeroesIn Set.univ (Set.Ioc 0 t))
      (fun ρ ↦ f ρ * (IEANTN.zetaOrder ρ : ℝ)), hset]

/-- Under RH up to `t`, weighting a zero sum by `x^{Re ρ}` multiplies it by `√x`. -/
theorem zsum_weight_sqrt {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x)
    (hRH : IEANTN.RiemannHypothesisUpTo t) (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f ρ * x ^ ρ.re)
      = Real.sqrt x * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) f := by
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
  have hre := CH2Section7A.re_eq_half_of_RH hRH hρ'.2.2 hρ'.2.1.1 hρ'.2.1.2
  rw [hre, show (1 : ℝ) / 2 = 1 / 2 from rfl, ← Real.sqrt_eq_rpow]
  ring

set_option maxHeartbeats 1000000 in
/-- **`prop:sagaro` at the height chosen by `lem:hardin`.** -/
theorem sagaro_at_t (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x σ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    ∃ t ∈ Set.Icc (T - 1 / 2) T,
      |CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
        ≤ Real.pi / t
          + (1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) ^ 2
              - 1.001 / (6 * Real.pi) * Real.log (t / (2 * Real.pi))) / Real.sqrt x
          + 2 * (12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
              + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x
              + Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3) / t ^ 2
          + 2 * Real.pi / (t * x)
              * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have hx1 : (1000000 : ℝ) ≤ x := by linarith [show (1000000 : ℝ) ≤ 10 ^ 9 by norm_num]
  obtain ⟨t, ⟨ht1, ht2⟩, hTfree, hInt1, hInt2⟩ := hardin hH hrvm hsmall hv hfe (by linarith) hx9 hxT hRH
  have ht7 : (10 : ℝ) ^ 7 - 1 ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have ht4 : (4 : ℝ) ≤ t := by linarith [show (4 : ℝ) ≤ 10 ^ 7 by norm_num]
  have hRHt : IEANTN.RiemannHypothesisUpTo t := RH_mono ht2 hRH
  obtain ⟨l, hsig, hlT, hlδ⟩ := exists_ladder (by linarith : (4 : ℝ) < t)
  have hRC := CH2Section6.hRC_of_rvm hsmall l hlδ
  have hTfree' : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T := by rw [hlT]; exact hTfree
  have hlam : CH2Section6.lamOf l.T σ < 0 := CH2Section6.lamOf_neg l.hT hσ1
  have hsig0 : 0 ≤ l.sigmaOf (CH2Section6.lamOf l.T σ) := by
    rw [CH2Section6.sigmaOf_lamOf l hσ1]; exact hσ0
  -- `Z`: the zero sum, from `prop:vihuela`
  set V : ℝ := 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) ^ 2
    - 1.001 / (6 * Real.pi) * Real.log (t / (2 * Real.pi)) with hV
  have hZ : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      IEANTN.zetaZeroesSum (Set.Iic 1) (Set.Ioc l.δ l.T)
          (fun ρ ↦ ‖CH2Section6.omegaPlus l.T σ ρ + ε * I * CH2Section6.thetaTS l.T 1 ρ‖
            * x ^ ρ.re) ≤ Real.sqrt x * (V * (t / (2 * Real.pi))) := by
    intro ε hε
    have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    rw [hlδ, hlT, zsum_Iic_Ioc_eq hsmall, zsum_weight_sqrt ht0.le hx0 hRHt]
    have hvi := CH2Section7A.vihuela hcs hrvm hsmall hplatt (T := t) (σ := σ) (ξ := ε) ht7 hRHt
      (fun z hz ↦ fun h ↦ hTfree z hz (by rw [h]; exact abs_of_pos ht0)) hσ0 hσ1 hε1
    rw [← hV] at hvi
    have hS : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ ‖CH2Section6.omegaPlus t σ ρ + (ε : ℂ) * I * CH2Section6.thetaTS t 1 ρ‖)
        ≤ V * (t / (2 * Real.pi)) := by
      rw [← sub_nonneg] at hvi
      rw [← sub_nonneg]
      have e : V * (t / (2 * Real.pi))
          - IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
            (fun ρ ↦ ‖CH2Section6.omegaPlus t σ ρ + (ε : ℂ) * I * CH2Section6.thetaTS t 1 ρ‖)
          = (t / (2 * Real.pi)) * (V - 2 * Real.pi / t * IEANTN.zetaZeroesSum Set.univ
            (Set.Ioc 0 t) (fun ρ ↦ ‖CH2Section6.omegaPlus t σ ρ
              + (ε : ℂ) * I * CH2Section6.thetaTS t 1 ρ‖)) := by
        field_simp
      rw [e]
      exact mul_nonneg (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg x)
  -- `E`: the shift error, from `lem:hardin` and `norm_intC_le`
  set J : ℝ := 12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
    + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x with hJ
  set K : ℝ := Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 with hK
  have hE : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      CH2Section6.shiftError l (CH2Section6.lamOf l.T σ) ε x ≤ x / (Real.pi * t) * (J + K) := by
    intro ε hε
    have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    have hC := CH2Section6.norm_intC_le hfe hdig hk hneg h2v l hlδ hlam hε1 (by rw [hlT]; exact ht4)
      hsig0 hRC hx1
    rw [hlT] at hC ⊢
    rw [CH2Section6.shiftError, hlT]
    have hKx : (Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3) / t
        = x * K / t := by rw [hK]; field_simp; try ring
    rw [hKx] at hC
    have e : x / (Real.pi * t) * (J + K)
        = 1 / (2 * Real.pi) * (1 / t * (x * J + x * J) + 2 * (x * K / t)) := by
      field_simp
      try ring
    rw [e]
    have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hI1 : (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u))
        ≤ x * J := hInt1
    have hI2 : (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u))
        ≤ x * J := by
      refine le_trans (le_of_eq ?_) hInt2
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
      congr 2
      try push_cast
      try ring
    have hle : 1 / t * ((∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u))
          + ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u))
        ≤ 1 / t * (x * J + x * J) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  -- apply `svm_abs_bound`
  have hmain := CH2Section6.svm_abs_bound hfe hdig hsig hTfree' hRC hσ0 hσ1 hσζ
    (x₀ := 2) (by norm_num) (by linarith [show (2 : ℝ) < 10 ^ 9 by norm_num]) hZ hE
  rw [hlT] at hmain
  refine ⟨t, ⟨ht1, ht2⟩, hmain.trans (le_of_eq ?_)⟩
  set r : ℝ := Real.sqrt x with hr
  have hx' : x = r * r := (Real.mul_self_sqrt hx0.le).symm
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hx0
  have e1 : 2 * Real.pi / (t * x) * (r * (V * (t / (2 * Real.pi)))) = V / r := by
    rw [hx']
    field_simp
    try ring
  have e2 : 2 * Real.pi / (t * x) * (x / (Real.pi * t) * (J + K)) = 2 * (J + K) / t ^ 2 := by
    field_simp
    try ring
  have e3 : 2 * Real.pi / (t * x)
      * (r * (V * (t / (2 * Real.pi)))
        + (1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))
        + x / (Real.pi * t) * (J + K))
      = 2 * Real.pi / (t * x) * (r * (V * (t / (2 * Real.pi))))
        + 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
        + 2 * Real.pi / (t * x) * (x / (Real.pi * t) * (J + K)) := by ring
  rw [e3, e1, e2, hV, hJ, hK]
  ring

/-! ### `lem:cothder` and the passage from `t` to `T` -/

/-- `sinh w ≤ w cosh w` for `w ≥ 0`: the derivative of `w cosh w - sinh w` is `w sinh w ≥ 0`. -/
theorem sinh_le_mul_cosh {w : ℝ} (hw : 0 ≤ w) : Real.sinh w ≤ w * Real.cosh w := by
  have hd : ∀ v : ℝ, HasDerivAt (fun u : ℝ ↦ u * Real.cosh u - Real.sinh u) (v * Real.sinh v) v := by
    intro v
    have h1 : HasDerivAt (fun u : ℝ ↦ u * Real.cosh u) (1 * Real.cosh v + v * Real.sinh v) v :=
      (hasDerivAt_id v).mul (Real.hasDerivAt_cosh v)
    exact (h1.sub (Real.hasDerivAt_sinh v)).congr_deriv (by ring)
  have hnn : ∀ v : ℝ, 0 ≤ v * Real.sinh v := by
    intro v
    rcases le_total 0 v with h | h
    · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr h)
    · nlinarith [Real.sinh_nonpos_iff.mpr h]
  have hmono : Monotone (fun u : ℝ ↦ u * Real.cosh u - Real.sinh u) :=
    monotone_of_deriv_nonneg (fun v ↦ (hd v).differentiableAt)
      (fun v ↦ by rw [(hd v).deriv]; exact hnn v)
  have h0 := hmono hw
  simp only [zero_mul, Real.sinh_zero, sub_zero, sub_self] at h0
  linarith

/-- `y coth y`, on the real line. -/
noncomputable def ycoth (y : ℝ) : ℝ := y * Real.cosh y / Real.sinh y

theorem hasDerivAt_ycoth {v : ℝ} (hv : 0 < v) :
    HasDerivAt ycoth (Real.cosh v / Real.sinh v - v / Real.sinh v ^ 2) v := by
  have hs : Real.sinh v ≠ 0 := (Real.sinh_pos_iff.mpr hv).ne'
  have h := ((hasDerivAt_id v).mul (Real.hasDerivAt_cosh v)).div (Real.hasDerivAt_sinh v) hs
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, id, one_mul]
  have hsq := Real.cosh_sq v
  field_simp
  linear_combination (-v) * hsq

/-- **`lem:cothder`, first half.** `|(y coth y)'| ≤ y` for `y > 0`. -/
theorem abs_deriv_ycoth_le {v : ℝ} (hv : 0 < v) :
    |Real.cosh v / Real.sinh v - v / Real.sinh v ^ 2| ≤ v := by
  have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have hs2 : 0 < Real.sinh v ^ 2 := by positivity
  have hc : 0 < Real.cosh v := Real.cosh_pos v
  have e : Real.cosh v / Real.sinh v - v / Real.sinh v ^ 2
      = (Real.sinh v * Real.cosh v - v) / Real.sinh v ^ 2 := by field_simp
  rw [e, abs_le]
  constructor
  · have h0 : 0 ≤ (Real.sinh v * Real.cosh v - v) / Real.sinh v ^ 2 := by
      apply div_nonneg _ hs2.le
      have h2 := Real.self_le_sinh_iff.mpr (by linarith : (0 : ℝ) ≤ 2 * v)
      rw [Real.sinh_two_mul] at h2
      linarith
    linarith
  · rw [div_le_iff₀ hs2]
    have h1 := sinh_le_mul_cosh hv.le
    have hsq := Real.cosh_sq v
    nlinarith [mul_le_mul_of_nonneg_right h1 hc.le]

/-- **The main term moves from `t` to `T` at a cost of `π a (1/t - 1/T)/t`**, `a = π(1-σ)`. -/
theorem coth_main_shift {σ t T : ℝ} (hσ1 : σ < 1) (ht : 0 < t) (htT : t ≤ T) :
    |Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
        - Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))|
      ≤ Real.pi * (Real.pi * (1 - σ)) * (1 / t - 1 / T) / t := by
  have hπ := Real.pi_pos
  have hT : 0 < T := by linarith
  set a : ℝ := Real.pi * (1 - σ) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hyt : 0 < a / t := by positivity
  have hyT : 0 < a / T := by positivity
  have hle : a / T ≤ a / t := by
    apply div_le_div_of_nonneg_left ha0.le ht htT
  -- rewrite both sides through `ycoth`
  have hrw : ∀ u : ℝ, 0 < u → Real.pi / u * (Real.cosh (a / u) / Real.sinh (a / u))
      = Real.pi / a * ycoth (a / u) := by
    intro u hu
    have hs : Real.sinh (a / u) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    rw [ycoth]
    field_simp
    try ring
  rw [hrw t ht, hrw T hT, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / a)]
  -- the mean value theorem on `[a/T, a/t]`
  have hmvt : |ycoth (a / t) - ycoth (a / T)| ≤ (a / t) * |a / t - a / T| := by
    have hsub : ∀ y ∈ Set.Icc (a / T) (a / t), 0 < y := fun y hy ↦ lt_of_lt_of_le hyT hy.1
    have hd : ∀ y ∈ Set.Icc (a / T) (a / t), HasDerivWithinAt ycoth
        (Real.cosh y / Real.sinh y - y / Real.sinh y ^ 2) (Set.Icc (a / T) (a / t)) y :=
      fun y hy ↦ (hasDerivAt_ycoth (hsub y hy)).hasDerivWithinAt
    have hb : ∀ y ∈ Set.Icc (a / T) (a / t),
        ‖Real.cosh y / Real.sinh y - y / Real.sinh y ^ 2‖ ≤ a / t := by
      intro y hy
      rw [Real.norm_eq_abs]
      exact (abs_deriv_ycoth_le (hsub y hy)).trans hy.2
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _)
      (Set.left_mem_Icc.mpr hle) (Set.right_mem_Icc.mpr hle)
    simpa [Real.norm_eq_abs] using this
  have he : Real.pi / a * ((a / t) * |a / t - a / T|)
      = Real.pi * a * (1 / t - 1 / T) / t := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a / t - a / T)]
    field_simp
    try ring
  calc Real.pi / a * |ycoth (a / t) - ycoth (a / T)|
      ≤ Real.pi / a * ((a / t) * |a / t - a / T|) := by
        exact mul_le_mul_of_nonneg_left hmvt (by positivity)
    _ = _ := he

set_option maxHeartbeats 1000000 in
/-- **`prop:sagaro` with the main term at `T`.** `sagaro_at_t` plus `coth_main_shift`; the error
is still expressed in terms of the chosen `t`. -/
theorem sagaro_shifted (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x σ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    ∃ t ∈ Set.Icc (T - 1 / 2) T,
      |CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
        ≤ Real.pi / t
          + (1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) ^ 2
              - 1.001 / (6 * Real.pi) * Real.log (t / (2 * Real.pi))) / Real.sqrt x
          + 2 * (12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
              + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x
              + Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3) / t ^ 2
          + 2 * Real.pi / (t * x)
              * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
          + Real.pi ^ 2 / (2 * t ^ 2 * T) := by
  have hπ := Real.pi_pos
  obtain ⟨t, ⟨ht1, ht2⟩, hbd⟩ := sagaro_at_t hfe hdig hk hneg h2v hv hcs hrvm hsmall hplatt hH
    hT hx9 hxT hRH hσ0 hσ1 hσζ
  have ht0 : (0 : ℝ) < t := by
    have : (0 : ℝ) < 10 ^ 7 := by norm_num
    linarith
  refine ⟨t, ⟨ht1, ht2⟩, ?_⟩
  have hshift := coth_main_shift (σ := σ) (t := t) (T := T) hσ1 ht0 ht2
  have hnum : Real.pi * (Real.pi * (1 - σ)) * (1 / t - 1 / T) / t ≤ Real.pi ^ 2 / (2 * t ^ 2 * T) := by
    have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
    have h1 : 1 / t - 1 / T = (T - t) / (t * T) := by field_simp
    rw [h1]
    have h2 : (T - t) / (t * T) ≤ (1 / 2) / (t * T) := by
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h3 : Real.pi * (Real.pi * (1 - σ)) ≤ Real.pi ^ 2 := by nlinarith
    have h4 : (0 : ℝ) ≤ (T - t) / (t * T) := by
      apply div_nonneg (by linarith) (by positivity)
    calc Real.pi * (Real.pi * (1 - σ)) * ((T - t) / (t * T)) / t
        ≤ Real.pi ^ 2 * ((T - t) / (t * T)) / t := by
          apply div_le_div_of_nonneg_right _ ht0.le
          exact mul_le_mul_of_nonneg_right h3 h4
      _ ≤ Real.pi ^ 2 * ((1 / 2) / (t * T)) / t := by
          apply div_le_div_of_nonneg_right _ ht0.le
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.pi ^ 2 / (2 * t ^ 2 * T) := by field_simp; try ring
  have htri : |CH2Section6.Svm σ x / x ^ (1 - σ)
      - (Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
        - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
      ≤ |CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
        + |Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - Real.pi / T
              * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))| := by
    have := abs_add_le (CH2Section6.Svm σ x / x ^ (1 - σ)
      - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
        - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1)))
      (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
        - Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T)
          / Real.sinh (Real.pi * (1 - σ) / T)))
    calc _ = |(CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1)))
          + (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t)
              / Real.sinh (Real.pi * (1 - σ) / t))
            - Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T)
              / Real.sinh (Real.pi * (1 - σ) / T)))| := by ring_nf
      _ ≤ _ := this
  linarith

/-! ### The numeric collapse: from the height `t` to `T` -/

theorem log_two_pi_le : Real.log (2 * Real.pi) ≤ 1.9 := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  rw [Real.log_le_iff_le_exp (by positivity), show (1.9 : ℝ) = (1 : ℕ) + 0.9 by norm_num,
    Real.exp_add]
  have h1 := (CH2Section7A.exp_nat_bounds 1).1
  have hs := CH2Section7A.exp_small_ge (x := 0.9) (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.exp 0.9 := (Real.exp_pos _).le
  calc 2 * Real.pi ≤ 2 * 3.15 := by linarith
    _ ≤ (2.7182818283 : ℝ) ^ 1 * (1 + 0.9 + 0.9 ^ 2 / 2 + 0.9 ^ 3 / 6 + 0.9 ^ 4 / 24) := by
        norm_num
    _ ≤ (2.7182818283 : ℝ) ^ 1 * Real.exp 0.9 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ Real.exp ((1 : ℕ) : ℝ) * Real.exp 0.9 := mul_le_mul_of_nonneg_right h1 h0

/-- `log T ≤ 2√T`, hence `(log T + 10)² ≤ 9T` once `T ≥ 64`. -/
theorem log_add_ten_sq_le {T : ℝ} (hT : 64 ≤ T) : (Real.log T + 10) ^ 2 ≤ 9 * T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have h8 : (8 : ℝ) ≤ Real.sqrt T := by
    rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hT
  have hlog : Real.log T ≤ 2 * Real.sqrt T - 2 := by
    have h1 : Real.log (Real.sqrt T) ≤ Real.sqrt T - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (Real.sqrt T) = Real.log T / 2 := Real.log_sqrt hT0.le
    rw [h2] at h1
    linarith
  have hR0 : 0 ≤ Real.log T + 10 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ T by linarith)
    linarith
  have hR3 : Real.log T + 10 ≤ 3 * Real.sqrt T := by linarith
  calc (Real.log T + 10) ^ 2 ≤ (3 * Real.sqrt T) ^ 2 := by
        exact pow_le_pow_left₀ hR0 hR3 2
    _ = 9 * T := by rw [mul_pow, Real.sq_sqrt hT0.le]; ring

set_option maxHeartbeats 4000000 in
/-- **`prop:sagaro`, with the leftover margin kept.** The error terms of `sagaro_shifted` collapse
into `π/(T-1)` and the `prop:vihuela` block; the `1.001` in the latter pays for everything else on
the `1/√x` side and still leaves `0.0005/√x`, which `Corollary 1.2` needs at `σ = 0` to absorb
`ζ'/ζ(0) = log 2π`. -/
theorem sagaro_slack (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x σ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    |CH2Section6.Svm σ x / x ^ (1 - σ)
        - (Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
          - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
      ≤ Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
            - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) - 0.0005) / Real.sqrt x := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  obtain ⟨t, ⟨ht1, ht2⟩, hbd⟩ := sagaro_shifted hfe hdig hk hneg h2v hv hcs hrvm hsmall hplatt hH
    hT hx9 hxT hRH hσ0 hσ1 hσζ
  have h107 : (10000000 : ℝ) = (10 : ℝ) ^ 7 := by norm_num
  have h109 : (1000000000 : ℝ) = (10 : ℝ) ^ 9 := by norm_num
  have hT0 : (10000000 : ℝ) ≤ T := by rw [h107] at *; linarith
  have hx0 : (1000000000 : ℝ) ≤ x := by rw [h109]; exact hx9
  have hxpos : (0 : ℝ) < x := by linarith
  have ht0 : (9999999 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  refine hbd.trans ?_
  -- names
  set R : ℝ := Real.log T with hRdef
  set L : ℝ := Real.log x with hLdef
  set y : ℝ := Real.log (T / (2 * Real.pi)) with hydef
  set z : ℝ := Real.log (t / (2 * Real.pi)) with hzdef
  set s : ℝ := Real.sqrt x with hsdef
  have hs0 : (0 : ℝ) < s := Real.sqrt_pos.mpr hxpos
  -- the logarithms
  have hR16 : 16.1 ≤ R := by
    have h1 : Real.log ((10 : ℝ) ^ 7) ≤ R := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [log_ten_ge]
  have hL20 : 20.7 ≤ L := by
    have h1 : Real.log ((10 : ℝ) ^ 9) ≤ L := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [log_ten_ge]
  have hRL : R ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hL0 : (0 : ℝ) < L := by linarith
  have hzy : z ≤ y := Real.log_le_log (by positivity) (by gcongr)
  have hz135 : 13.5 ≤ z := by
    have hzeq : z = Real.log t - Real.log (2 * Real.pi) := by
      rw [hzdef, Real.log_div (by linarith) (by positivity)]
    have hlt : Real.log ((10 : ℝ) ^ 7 / 2) ≤ Real.log t :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow] at hlt
    push_cast at hlt
    linarith [log_ten_ge, log_two_pi_le, Real.log_two_lt_d9]
  have hy135 : 13.5 ≤ y := by linarith
  -- the `1/√x` block
  have hslack : 4 * (R + 10) ^ 2 / t ^ 2 + 0.0005 ≤ 0.001 / (6 * Real.pi) * z := by
    have h1 : (R + 10) ^ 2 ≤ 9 * T := log_add_ten_sq_le (by linarith)
    have h2 : T ^ 2 / 2 ≤ t ^ 2 := by nlinarith
    have h3 : 4 * (R + 10) ^ 2 / t ^ 2 ≤ 72 / T := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    have h4 : (72 : ℝ) / T ≤ 0.0000072 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h5 : 0.001 / (6 * Real.pi) * z ≥ 0.001 / (6 * Real.pi) * 13.5 := by
      apply mul_le_mul_of_nonneg_left hz135 (by positivity)
    have h6 : (0.0007 : ℝ) ≤ 0.001 / (6 * Real.pi) * 13.5 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hkey2 : (1 / (2 * Real.pi) * z ^ 2 - 1.001 / (6 * Real.pi) * z) / s
        + 4 * (R + 10) ^ 2 / t ^ 2 / s
      ≤ (1 / (2 * Real.pi) * y ^ 2 - 1 / (6 * Real.pi) * y - 0.0005) / s := by
    rw [← add_div, div_le_div_iff_of_pos_right hs0]
    have hbracket : 0 ≤ 1 / (2 * Real.pi) * (y ^ 2 - z ^ 2) - 1 / (6 * Real.pi) * (y - z) := by
      have h1 : 1 / (6 * Real.pi) * (y - z) ≤ 1 / (2 * Real.pi) * (y ^ 2 - z ^ 2) := by
        have hyz : 0 ≤ y - z := by linarith
        have h2 : y ^ 2 - z ^ 2 = (y - z) * (y + z) := by ring
        rw [h2]
        have h3 : 1 / (6 * Real.pi) ≤ 1 / (2 * Real.pi) * (y + z) := by
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) / (2 * Real.pi) * (y + z) * (6 * Real.pi) = 3 * (y + z) := by
            field_simp; ring
          rw [this]
          linarith
        nlinarith
      linarith
    have he : 1 / (2 * Real.pi) * y ^ 2 - 1 / (6 * Real.pi) * y
        - (1 / (2 * Real.pi) * z ^ 2 - 1.001 / (6 * Real.pi) * z)
        = (1 / (2 * Real.pi) * (y ^ 2 - z ^ 2) - 1 / (6 * Real.pi) * (y - z))
          + 0.001 / (6 * Real.pi) * z := by ring
    linarith
  -- the `π/T` block
  have htriv : 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
      ≤ 0.001 / t ^ 2 := by
    have hx2 : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
      rw [Real.rpow_neg hxpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        one_div]
    rw [hx2]
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hx2ne : x ^ 2 - 1 ≠ 0 := by nlinarith
    have hne : 1 - 1 / x ^ 2 ≠ 0 := by
      have h9 : 1 / x ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
      intro hc
      rw [sub_eq_zero] at hc
      linarith [hc.symm.le]
    have hd : 1 / x ^ 2 / (1 - 1 / x ^ 2) = 1 / (x ^ 2 - 1) := by
      field_simp
      try ring
    rw [hd]
    have h1 : 1 / (x ^ 2 - 1) ≤ 2 / x ^ 2 := by
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
    have h2 : 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) ≤ 0.51 / x := by
      have e : 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi))
          = 2 * Real.pi / (t * x) + 1 / (2 * x) := by field_simp; ring
      rw [e]
      have h3 : 2 * Real.pi / (t * x) ≤ 0.01 / x := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have h4 : 1 / (2 * x) = 0.5 / x := by field_simp; ring
      rw [h4] at *
      have : (0.01 : ℝ) / x + 0.5 / x = 0.51 / x := by field_simp; ring
      linarith
    have h5 : 0 ≤ 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) := by positivity
    have h6 : 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (1 / (x ^ 2 - 1)))
        = 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) * (1 / (x ^ 2 - 1)) := by ring
    rw [h6]
    have h7 : 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) * (1 / (x ^ 2 - 1))
        ≤ 0.51 / x * (2 / x ^ 2) := by
      exact mul_le_mul h2 h1 (div_nonneg (by norm_num) (by nlinarith)) (by positivity)
    have h8 : (0.51 : ℝ) / x * (2 / x ^ 2) ≤ 0.001 / t ^ 2 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have htx : t ≤ x := by linarith
      have h9 : t ^ 2 ≤ x ^ 2 := by nlinarith
      nlinarith [h9, mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ x - 1020)]
    linarith
  have hcoth : Real.pi ^ 2 / (2 * t ^ 2 * T) ≤ 0.000001 / t ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.pi ^ 2 ≤ 0.000002 * T := by nlinarith
    calc Real.pi ^ 2 * t ^ 2 ≤ (0.000002 * T) * t ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
      _ = 0.000001 * (2 * t ^ 2 * T) := by ring
  have hI : 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
        + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) ≤ 1.51 := by
    have hγ := Real.eulerMascheroniConstant_lt_two_thirds
    have hL2 : (20.7 : ℝ) * L ≤ L ^ 2 := by nlinarith
    have hL3 : (20.7 : ℝ) ^ 2 * L ≤ L ^ 3 := by nlinarith
    have h1 : 12.5 * R / L ^ 2 ≤ 0.605 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : 62 * R / L ^ 3 ≤ 0.145 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h3 : Real.eulerMascheroniConstant / L ^ 2 ≤ 0.0016 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h4 : (1.8 : ℝ) / L ^ 3 ≤ 0.0003 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hkey1 : Real.pi / t
      + 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
          + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2
      + 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
      + Real.pi ^ 2 / (2 * t ^ 2 * T)
      ≤ Real.pi / (T - 1) := by
    have hIt : 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
        + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2 ≤ 1.51 / t ^ 2 := by
      apply div_le_div_of_nonneg_right hI (by positivity)
    have hsum : 1.51 / t ^ 2 + 0.001 / t ^ 2 + 0.000001 / t ^ 2 ≤ Real.pi / 2 / t ^ 2 := by
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have hq1 : (0 : ℝ) < (T - 1) * (T - 1 / 2) := mul_pos (by linarith) (by linarith)
    have hq2 : (T - 1) * (T - 1 / 2) ≤ t ^ 2 := by nlinarith [ht1, hT0]
    have hle : Real.pi / 2 / t ^ 2 ≤ Real.pi / 2 / ((T - 1) * (T - 1 / 2)) :=
      div_le_div_of_nonneg_left (by positivity) hq1 hq2
    have hpt : Real.pi / t ≤ Real.pi / (T - 1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) ht1
    have hsplit : Real.pi / (T - 1 / 2) + Real.pi / 2 / ((T - 1) * (T - 1 / 2))
        = Real.pi / (T - 1) := by
      have hT1 : (T : ℝ) - 1 ≠ 0 := by intro h; linarith
      have hT2 : (T : ℝ) - 1 / 2 ≠ 0 := by intro h; linarith
      rw [div_add_div _ _ hT2 (ne_of_gt hq1),
        div_eq_div_iff (mul_ne_zero hT2 (ne_of_gt hq1)) hT1]
      ring
    linarith
  -- combine
  have hJsplit : 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3 + 2 * (R + 10) ^ 2 / s
        + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2
      = 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
          + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2
        + 4 * (R + 10) ^ 2 / t ^ 2 / s := by
    field_simp
    ring
  rw [hJsplit]
  linarith

/-- **`prop:sagaro`**, in the paper's form: `sagaro_slack` with the margin dropped. -/
theorem sagaro (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x σ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    |CH2Section6.Svm σ x / x ^ (1 - σ)
        - (Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
          - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
      ≤ Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
            - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi))) / Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h := sagaro_slack hfe hdig hk hneg h2v hv hcs hrvm hsmall hplatt hH hT hx9 hxT hRH hσ0 hσ1 hσζ
  have hle : (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
        - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) - 0.0005) / Real.sqrt x
      ≤ (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
        - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi))) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith) hs0.le
  linarith

end CH2Section9
