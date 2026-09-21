/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section9
import IEANTN.Nodes.CH2.v1.Conclusions

/-!
# Section 9: the case `σ = 1`

`prop:sagaro` is proved for `0 ≤ σ < 1`; the `∑_{n ≤ x} Λ(n)/n` corollary is its `σ = 1` case. The
right-hand side of `CH2Section9.sagaro` does not involve `σ`, so it is enough to compute the limit
of the left-hand side as `σ → 1⁻`. Both halves of the main term blow up like `1/(1-σ)` and the
poles cancel:

`(π/T) coth(π(1-σ)/T) - (ζ'/ζ)(σ) x^{σ-1} = (g(u) - x^{σ-1})/(1-σ) - logDeriv ζ₁(σ) x^{σ-1}`

with `g(y) = y coth y` and `u = π(1-σ)/T`. Here `g(u) - 1 = O(u²)`, `(1 - x^{σ-1})/(1-σ) → log x`,
and `logDeriv ζ₁` is continuous at `1` with value `γ` — so the limit is `log x - γ`.

This file carries the four analytic ingredients and the limit of the main term; the packaging of
`Corollary 1.2` comes after.
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section9

/-! ### `g(y) = y coth y` near `0` -/

theorem one_le_ycoth {u : ℝ} (hu : 0 < u) : 1 ≤ ycoth u := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  rw [ycoth, le_div_iff₀ hs, one_mul]
  exact sinh_le_mul_cosh hu.le

theorem ycoth_le_cosh {u : ℝ} (hu : 0 < u) : ycoth u ≤ Real.cosh u := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  rw [ycoth, div_le_iff₀ hs]
  have h1 : u ≤ Real.sinh u := Real.self_le_sinh_iff.mpr hu.le
  nlinarith

theorem cosh_le_one_add_sq {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : Real.cosh u ≤ 1 + u ^ 2 := by
  have he1 : Real.exp u ≤ 1 + u + u ^ 2 / 2 + u ^ 3 * 4 / 18 :=
    CH2Section7A.exp_small_le h0 h1
  have he2 : Real.exp (-u) ≤ 1 - u + u ^ 2 := by
    have hpos : (0 : ℝ) < 1 + u := by linarith
    have hge : 1 + u ≤ Real.exp u := Real.add_one_le_exp u |>.trans_eq' (by ring)
    have h3 : Real.exp (-u) = 1 / Real.exp u := by
      rw [Real.exp_neg, one_div]
    rw [h3, div_le_iff₀ (Real.exp_pos u)]
    have h4 : (1 - u + u ^ 2) * (1 + u) = 1 + u ^ 3 := by ring
    nlinarith [Real.exp_pos u, pow_nonneg h0 3]
  rw [Real.cosh_eq]
  nlinarith [pow_nonneg h0 3]

/-- `|g(u) - 1| ≤ u²` for `0 < u ≤ 1`: the remainder of the `coth` pole. -/
theorem abs_ycoth_sub_one_le {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) : |ycoth u - 1| ≤ u ^ 2 := by
  rw [abs_le]
  have hlo := one_le_ycoth h0
  have hhi := (ycoth_le_cosh h0).trans (cosh_le_one_add_sq h0.le h1)
  constructor <;> nlinarith [sq_nonneg u]

/-! ### `ζ'/ζ` near `1` -/

theorem logDeriv_zeta₁_one : logDeriv riemannZeta₁ 1 = (Real.eulerMascheroniConstant : ℂ) := by
  rw [logDeriv_apply, deriv_riemannZeta₁_one, riemannZeta₁_one, div_one]

theorem continuousAt_logDeriv_zeta₁ : ContinuousAt (logDeriv riemannZeta₁) 1 := by
  have hd : ContinuousAt (deriv riemannZeta₁) 1 := by
    have hA : AnalyticAt ℂ riemannZeta₁ 1 :=
      differentiable_riemannZeta₁.differentiableOn.analyticAt univ_mem
    exact hA.deriv.continuousAt
  have hz : ContinuousAt riemannZeta₁ 1 := differentiable_riemannZeta₁.continuous.continuousAt
  have hne : riemannZeta₁ 1 ≠ 0 := by rw [riemannZeta₁_one]; norm_num
  exact (hd.div hz hne).congr (by filter_upwards with s using (logDeriv_apply _ _).symm)

/-- `ζ'/ζ(σ) = logDeriv ζ₁(σ) + 1/(1-σ)` off the pole and the zeros. -/
theorem logDeriv_zeta_eq {σ : ℝ} (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = logDeriv riemannZeta₁ (σ : ℂ) + ((1 / (1 - σ) : ℝ) : ℂ) := by
  have h1 : ((σ : ℝ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h := CH2ZetaInstance.logDeriv_riemannZeta₁_eq h1 hσζ
  rw [h, logDeriv_apply]
  have hne : ((σ : ℝ) : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h1
  have e : (((σ : ℝ) : ℂ) - 1)⁻¹ = ((1 / (1 - σ) : ℝ) : ℂ) → True := fun _ ↦ trivial
  have : (((σ : ℝ) : ℂ) - 1)⁻¹ = -((1 / (1 - σ) : ℝ) : ℂ) := by
    push_cast
    rw [eq_comm, neg_eq_iff_eq_neg, ← inv_neg]
    congr 1
    ring
  rw [this]
  ring

/-! ### The slope of `x^{σ-1}` -/

theorem tendsto_rpow_slope {x : ℝ} (hx : 0 < x) :
    Tendsto (fun σ : ℝ ↦ (x ^ (σ - 1) - 1) / (σ - 1)) (𝓝[≠] 1) (𝓝 (Real.log x)) := by
  have h3 : ∀ σ : ℝ, x ^ (σ - 1) = Real.exp ((σ - 1) * Real.log x) := fun σ ↦ by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  have hd : HasDerivAt (fun σ : ℝ ↦ x ^ (σ - 1)) (Real.log x) 1 := by
    have h2 : HasDerivAt (fun σ : ℝ ↦ (σ - 1) * Real.log x) (Real.log x) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 1).mul_const (Real.log x)
    have h1 := h2.exp
    simp only [sub_self, zero_mul, Real.exp_zero, one_mul] at h1
    refine (h1.congr_deriv rfl).congr_of_eventuallyEq ?_
    filter_upwards with σ using (h3 σ)
  have hslope := hd.tendsto_slope
  refine hslope.congr fun σ ↦ ?_
  rw [slope_def_field]
  norm_num

/-! ### The sum side -/

open ArithmeticFunction in
theorem Svm_eq_sum {σ x : ℝ} (hσ : σ < 1) :
    CH2Section6.Svm σ x
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) ^ σ := by
  rw [CH2Section6.Svm, CH2Sol.S, if_pos hσ]

open ArithmeticFunction in
theorem continuous_partial_sum (x : ℝ) :
    Continuous (fun σ : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) ^ σ) := by
  refine continuous_finsetSum _ fun n hn ↦ ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  simp_rw [Real.rpow_def_of_pos hpos]
  exact continuous_const.div (by fun_prop) (fun σ ↦ Real.exp_ne_zero _)

open ArithmeticFunction in
theorem partial_sum_one (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) ^ (1 : ℝ)
      = ∑ n ∈ Finset.Iic ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) := by
  simp_rw [Real.rpow_one]
  refine Finset.sum_subset (fun n hn ↦ Finset.mem_Iic.mpr (Finset.mem_Icc.mp hn).2) ?_
  intro n hn hn'
  have hn0 : n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h
    · exact absurd (Finset.mem_Icc.mpr ⟨h, Finset.mem_Iic.mp hn⟩) hn'
  simp [hn0]

open ArithmeticFunction in
theorem tendsto_Svm {x : ℝ} (hx : 0 < x) :
    Tendsto (fun σ : ℝ ↦ CH2Section6.Svm σ x / x ^ (1 - σ)) (𝓝[<] 1)
      (𝓝 (∑ n ∈ Finset.Iic ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ))) := by
  have hcont : ContinuousAt
      (fun σ : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) ^ σ) / x ^ (1 - σ)) 1 := by
    refine (continuous_partial_sum x).continuousAt.div ?_ ?_
    · have : ContinuousAt (fun σ : ℝ ↦ Real.exp (Real.log x * (1 - σ))) 1 := by fun_prop
      refine this.congr ?_
      filter_upwards with σ using (Real.rpow_def_of_pos hx _).symm
    · rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero]
      norm_num
  have hval : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) ^ (1 : ℝ)) / x ^ (1 - 1 : ℝ)
      = ∑ n ∈ Finset.Iic ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) := by
    rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero, div_one, partial_sum_one]
  rw [← hval]
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [Svm_eq_sum hσ]

/-! ### The main term -/

theorem tendsto_main {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    Tendsto (fun σ : ℝ ↦ Real.pi / T
        * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
        - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1)) (𝓝[<] 1)
      (𝓝 (Real.log x - Real.eulerMascheroniConstant)) := by
  have hπ := Real.pi_pos
  -- the three pieces
  have hA : Tendsto (fun σ : ℝ ↦ (ycoth (Real.pi * (1 - σ) / T) - 1) / (1 - σ)) (𝓝[<] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun σ : ℝ ↦ (Real.pi / T) ^ 2 * (1 - σ)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (1 : ℝ) - min 1 (T / Real.pi) < 1 by
          have : 0 < min 1 (T / Real.pi) := lt_min one_pos (by positivity)
          linarith)).filter_mono nhdsWithin_le_nhds] with σ hσ hσ'
      have hσ1 : σ < 1 := hσ
      have h0 : 0 < 1 - σ := by linarith
      have hu0 : 0 < Real.pi * (1 - σ) / T := by positivity
      have hu1 : Real.pi * (1 - σ) / T ≤ 1 := by
        rw [div_le_one hT]
        have hm : 1 - σ ≤ T / Real.pi := by
          have := min_le_right (1 : ℝ) (T / Real.pi)
          linarith
        calc Real.pi * (1 - σ) ≤ Real.pi * (T / Real.pi) := by nlinarith
          _ = T := by field_simp
      have hb := abs_ycoth_sub_one_le hu0 hu1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos h0]
      rw [div_le_iff₀ h0]
      have hsq : (Real.pi * (1 - σ) / T) ^ 2 = (Real.pi / T) ^ 2 * (1 - σ) ^ 2 := by
        field_simp
      calc |ycoth (Real.pi * (1 - σ) / T) - 1| ≤ (Real.pi * (1 - σ) / T) ^ 2 := hb
        _ = (Real.pi / T) ^ 2 * (1 - σ) ^ 2 := hsq
        _ = (Real.pi / T) ^ 2 * (1 - σ) * (1 - σ) := by ring
    · have : Tendsto (fun σ : ℝ ↦ (Real.pi / T) ^ 2 * (1 - σ)) (𝓝 1) (𝓝 0) := by
        have : ContinuousAt (fun σ : ℝ ↦ (Real.pi / T) ^ 2 * (1 - σ)) 1 := by fun_prop
        simpa using this.tendsto
      exact this.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun σ : ℝ ↦ (1 - x ^ (σ - 1)) / (1 - σ)) (𝓝[<] 1) (𝓝 (Real.log x)) := by
    have h := (tendsto_rpow_slope hx).mono_left
      (nhdsWithin_mono 1 (fun σ (hσ : σ ∈ Iio 1) ↦ ne_of_lt hσ))
    refine h.congr fun σ ↦ ?_
    rw [show (1 : ℝ) - x ^ (σ - 1) = -(x ^ (σ - 1) - 1) by ring,
      show (1 : ℝ) - σ = -(σ - 1) by ring, neg_div_neg_eq]
  have hC : Tendsto (fun σ : ℝ ↦ (logDeriv riemannZeta₁ (σ : ℂ)).re * x ^ (σ - 1)) (𝓝[<] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
    have hcoe : ContinuousAt (fun σ : ℝ ↦ ((σ : ℝ) : ℂ)) 1 := Complex.continuous_ofReal.continuousAt
    have hcomp : ContinuousAt (fun σ : ℝ ↦ logDeriv riemannZeta₁ (σ : ℂ)) 1 := by
      refine ContinuousAt.comp ?_ hcoe
      rw [Complex.ofReal_one]
      exact continuousAt_logDeriv_zeta₁
    have h1 : ContinuousAt (fun σ : ℝ ↦ (logDeriv riemannZeta₁ (σ : ℂ)).re) 1 :=
      Complex.continuous_re.continuousAt.comp hcomp
    have h2 : ContinuousAt (fun σ : ℝ ↦ x ^ (σ - 1)) 1 := by
      have hE : ContinuousAt (fun σ : ℝ ↦ Real.exp (Real.log x * (σ - 1))) 1 := by fun_prop
      refine hE.congr ?_
      filter_upwards with σ using (Real.rpow_def_of_pos hx _).symm
    have hval : (logDeriv riemannZeta₁ (((1 : ℝ) : ℝ) : ℂ)).re * x ^ ((1 : ℝ) - 1)
        = Real.eulerMascheroniConstant := by
      rw [Complex.ofReal_one, logDeriv_zeta₁_one]
      simp
    have h3 : Tendsto (fun σ : ℝ ↦ (logDeriv riemannZeta₁ (σ : ℂ)).re * x ^ (σ - 1)) (𝓝 1)
        (𝓝 ((logDeriv riemannZeta₁ (((1 : ℝ) : ℝ) : ℂ)).re * x ^ ((1 : ℝ) - 1))) :=
      h1.tendsto.mul h2.tendsto
    rw [hval] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  have hlim := (hA.add hB).sub hC
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with σ hσ hσ0
  have hσ1 : σ < 1 := hσ
  have h0 : 0 < 1 - σ := by linarith
  have hζ : riemannZeta (σ : ℂ) ≠ 0 := CH2ZetaReal.riemannZeta_ne_zero_Ico hσ0.le hσ1
  have hL := logDeriv_zeta_eq hσ1 hζ
  have hre : (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      = (logDeriv riemannZeta₁ (σ : ℂ)).re + 1 / (1 - σ) := by
    rw [hL, Complex.add_re, Complex.ofReal_re]
  have hy : Real.pi / T
      * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
      = ycoth (Real.pi * (1 - σ) / T) / (1 - σ) := by
    rw [ycoth]
    field_simp
    try ring
  rw [hy, hre]
  field_simp
  try ring

/-! ### `prop:sagaro` at `σ = 1` -/

open ArithmeticFunction in
set_option maxHeartbeats 1000000 in
/-- **`prop:sagaro`, the `σ = 1` case**: the `∑_{n ≤ x} Λ(n)/n` bound, by letting `σ → 1⁻` in
`CH2Section9.sagaro`, whose right-hand side does not involve `σ`. -/
theorem sagaro_one (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T) :
    |(∑ n ∈ Finset.Iic ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ))
        - (Real.log x - Real.eulerMascheroniConstant)|
      ≤ Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
            - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi))) / Real.sqrt x := by
  have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have hlim := ((tendsto_Svm hx0).sub (tendsto_main hT0 hx0)).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with σ hσ hσ0
  have hσ1 : σ < 1 := hσ
  exact sagaro hfe hdig hk hneg h2v hv hcs hrvm hsmall hplatt hH hT hx9 hxT hRH hσ0.le hσ1
    (CH2ZetaReal.riemannZeta_ne_zero_Ico hσ0.le hσ1)

/-! ### `prop:sagaro` at `σ = 0`: Corollary 1.2 for `ψ` -/

/-- `ζ'/ζ(0) = log 2π`, from Mathlib's `ζ'(0) = -log(2π)/2` and `ζ(0) = -1/2`. -/
theorem logDeriv_zeta_zero :
    deriv riemannZeta 0 / riemannZeta 0 = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero,
    show ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity)]
  push_cast
  field_simp

open ArithmeticFunction in
theorem Svm_zero (x : ℝ) : CH2Section6.Svm 0 x = Chebyshev.psi x := by
  rw [Svm_eq_sum (by norm_num), Chebyshev.psi]
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Real.rpow_zero, div_one]

set_option maxHeartbeats 1000000 in
/-- **Corollary 1.2, the `ψ` estimate**, at `T ≥ 10⁷ + 1`. The `σ = 0` case of `prop:sagaro`: the
main term's `-ζ'/ζ(0) x^{-1} = -log(2π)/x` is paid for by the `0.0005/√x` that `sagaro_slack`
keeps back. -/
theorem corollary_1_2_psi_at (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T) :
    |Chebyshev.psi x - x * CH2.v1.mainFactor T|
      ≤ Real.pi / (T - 1) * x + CH2.v1.CT T * Real.sqrt x := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hζ0 : riemannZeta ((0 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_zero, riemannZeta_zero]
    norm_num
  have h := sagaro_slack hfe hdig hk hneg h2v hv hcs hrvm hsmall hplatt hH hT hx9 hxT hRH
    (σ := 0) le_rfl (by norm_num) hζ0
  -- rewrite the `σ = 0` main term
  rw [Svm_zero, Complex.ofReal_zero, logDeriv_zeta_zero] at h
  simp only [Complex.ofReal_re, sub_zero, zero_sub, mul_one] at h
  rw [Real.rpow_one] at h
  have hmf : Real.pi / T * (Real.cosh (Real.pi / T) / Real.sinh (Real.pi / T))
      = CH2.v1.mainFactor T := by
    have hs : Real.sinh (Real.pi / T) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    have hc : Real.cosh (Real.pi / T) ≠ 0 := (Real.cosh_pos _).ne'
    rw [CH2.v1.mainFactor, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hxinv : x ^ (-1 : ℝ) = 1 / x := by
    rw [Real.rpow_neg_one, one_div]
  rw [hmf, hxinv] at h
  -- multiply through by `x`
  have hmul : |x * (Chebyshev.psi x / x
        - (CH2.v1.mainFactor T - Real.log (2 * Real.pi) * (1 / x)))|
      ≤ x * (Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
          - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) - 0.0005) / Real.sqrt x) := by
    rw [abs_mul, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_left h hx0.le
  have he : x * (Chebyshev.psi x / x - (CH2.v1.mainFactor T - Real.log (2 * Real.pi) * (1 / x)))
      = Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi) := by
    field_simp
    ring
  have hrhs : x * (Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
          - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) - 0.0005) / Real.sqrt x)
      = Real.pi / (T - 1) * x + CH2.v1.CT T * Real.sqrt x - 0.0005 * Real.sqrt x := by
    have hxs : ∀ A : ℝ, x * (A / Real.sqrt x) = A * Real.sqrt x := by
      intro A
      field_simp
      linear_combination (-A) * hss
    rw [CH2.v1.CT, mul_add, hxs]
    ring
  rw [he, hrhs] at hmul
  -- absorb `log 2π`
  have hlog : Real.log (2 * Real.pi) ≤ 0.0005 * Real.sqrt x := by
    have h1 : Real.log (2 * Real.pi) ≤ 1.9 := log_two_pi_le
    have h2 : (31622 : ℝ) ≤ Real.sqrt x := by
      rw [show (31622 : ℝ) = Real.sqrt (31622 ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by nlinarith [show (10 : ℝ) ^ 9 = 1000000000 by norm_num])
    nlinarith
  have hlog0 : |Real.log (2 * Real.pi)| = Real.log (2 * Real.pi) :=
    abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))
  have habs : |Chebyshev.psi x - x * CH2.v1.mainFactor T|
      ≤ |Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi)|
        + Real.log (2 * Real.pi) := by
    calc |Chebyshev.psi x - x * CH2.v1.mainFactor T|
        = |(Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi))
            + -Real.log (2 * Real.pi)| := by ring_nf
      _ ≤ |Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi)|
            + |-Real.log (2 * Real.pi)| := abs_add_le _ _
      _ = |Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi)|
            + Real.log (2 * Real.pi) := by rw [abs_neg, hlog0]
  linarith

/-- **The node's first conclusion**, `CH2.v1.corollary_1_2_psi`, conditional on the imported node
conclusions. -/
theorem corollary_1_2_psi (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions) :
    CH2.v1.corollary_1_2_psi := by
  intro T x hT hRH hx
  exact corollary_1_2_psi_at hfe hdig hk hneg h2v hv hcs hrvm hsmall hplatt hH hT
    (le_of_lt (lt_of_le_of_lt (le_max_right T _) hx))
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx)) hRH

/-- **The node's second conclusion**, `CH2.v1.corollary_1_2_lambda_sum`: `sagaro_one` in the node's
own words. -/
theorem corollary_1_2_lambda_sum (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions) :
    CH2.v1.corollary_1_2_lambda_sum := by
  intro T x hT hRH hx
  rw [CH2.v1.lambdaSum, CH2.v1.CT]
  exact sagaro_one hfe hdig hk hneg h2v hv hcs hrvm hsmall hplatt hH hT
    (le_of_lt (lt_of_le_of_lt (le_max_right T _) hx))
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx)) hRH

end CH2Section9
