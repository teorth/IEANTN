/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section81Titch
import Section81
import GammaStrip
import IEANTN.Nodes.ZetaLogDeriv.v1.Conclusions

/-!
# Section 8.1: `lem:saghar` and `lem:adioso`, pointwise

For `s = 1 - u + it`:

* `0 ≤ u ≤ 3/2` (`saghar_pt`): `|ζ'/ζ(s)| ≤ (1/2 + u) A(t) + ∑_{|γ - t| ≤ 1/4} m_ρ / |s - ρ|`,
  with `A(t) = (4/π) log(t/2π) + 32 (2/5 log t + 4)`, from `prop:titch96A` (the non-`σ` part of
  its right-hand side is negative and is dropped);
* `u ≥ 3/2` (`adioso_pt`): `|ζ'/ζ(s)| ≤ 12 + 2t + u`, from the functional equation at `1 - s`.
  This is much cruder than `lem:adioso`, and costs nothing: after integration against
  `u x^{-u}` it is `O(t x^{-3/2})`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Nat

namespace CH2Section81

/-- `A(t)`, the coefficient of `3/2 - σ` in `prop:titch96A`. -/
noncomputable def titchA (t : ℝ) : ℝ :=
  4 / Real.pi * Real.log (t / (2 * Real.pi)) + 32 * (2 / 5 * Real.log t + 4)

open Classical in
/-- The zeros with ordinate in `(t - 1/4, t + 1/4]`, as a finset. -/
noncomputable def innerZ (t : ℝ) : Finset ℂ :=
  if h : (IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4))).Finite then h.toFinset
  else ∅

theorem innerZ_eq {t : ℝ} (hfin : (IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4))).Finite) :
    innerZ t = hfin.toFinset := by
  rw [innerZ, dif_pos hfin]

theorem saghar_pt (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    {t u : ℝ} (ht : 1000 ≤ t) (hu0 : 0 ≤ u) (hu : u ≤ 3 / 2)
    (hs : riemannZeta (((1 - u : ℝ) : ℂ) + t * I) ≠ 0)
    (hRH : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)), ρ.re = 1 / 2) :
    ‖deriv riemannZeta (((1 - u : ℝ) : ℂ) + t * I) / riemannZeta (((1 - u : ℝ) : ℂ) + t * I)‖
      ≤ (1 / 2 + u) * titchA t
        + ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) / Real.sqrt (|t - ρ.im| ^ 2 + (1 / 2 - u) ^ 2) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hT := titch96A hH hrvm hsmall hv (σ := 1 - u) ht (by linarith) (by linarith) hs hRH
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := t - 1 / 4) (b := t + 1 / 4) (by linarith)
  rw [zetaZeroesSum_eq_sum_C hfin] at hT
  rw [innerZ_eq hfin]
  set s : ℂ := ((1 - u : ℝ) : ℂ) + t * I with hs_def
  have hS : ‖∑ ρ ∈ hfin.toFinset, 1 / (s - ρ) * (IEANTN.zetaOrder ρ : ℂ)‖
      ≤ ∑ ρ ∈ hfin.toFinset,
          (IEANTN.zetaOrder ρ : ℝ) / Real.sqrt (|t - ρ.im| ^ 2 + (1 / 2 - u) ^ 2) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
    have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
    have hm := CH2Section7Z.zetaOrder_nonneg_of_mem
      (fun x hx ↦ show (0 : ℝ) < x by linarith [hx.1]) hρ'
    have hre := hRH ρ hρ'
    have hnorm : ‖s - ρ‖ = Real.sqrt (|t - ρ.im| ^ 2 + (1 / 2 - u) ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply, sq_abs]
      congr 1
      simp only [hs_def, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
        Complex.mul_im, hre]
      ring
    rw [norm_mul, norm_zetaOrder_cast hm, norm_div, norm_one, hnorm, div_mul_eq_mul_div, one_mul]
  have hA : (4 * (3 / 2 - (1 - u)) + 1 / 4) / Real.pi * Real.log (t / (2 * Real.pi))
        + (32 * (3 / 2 - (1 - u)) - 1) * (2 / 5 * Real.log t + 4) + 1.5053 + 0.016
      ≤ (1 / 2 + u) * titchA t := by
    have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hLt0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
    have hLt : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
      Real.log_le_log (by positivity) (div_le_self (by linarith) (by linarith))
    have hq : (1 / 4) / Real.pi ≤ 1 / 12 := by rw [div_le_iff₀ hπ]; linarith
    have h1 := mul_le_mul hq hLt hLt0 (by norm_num)
    have e : (4 * (3 / 2 - (1 - u)) + 1 / 4) / Real.pi
        = (1 / 2 + u) * (4 / Real.pi) + (1 / 4) / Real.pi := by ring
    rw [e, titchA]
    nlinarith
  have hdiff := norm_sub_norm_le (deriv riemannZeta s / riemannZeta s)
    (∑ ρ ∈ hfin.toFinset, 1 / (s - ρ) * (IEANTN.zetaOrder ρ : ℂ))
  have hT' : ‖deriv riemannZeta s / riemannZeta s
      - ∑ ρ ∈ hfin.toFinset, 1 / (s - ρ) * (IEANTN.zetaOrder ρ : ℂ)‖
      ≤ (4 * (3 / 2 - (1 - u)) + 1 / 4) / Real.pi * Real.log (t / (2 * Real.pi))
        + (32 * (3 / 2 - (1 - u)) - 1) * (2 / 5 * Real.log t + 4) + 1.5053 + 0.016 := hT
  linarith

/-! ### `u ≥ 3/2` -/

theorem norm_sq_sin (w : ℂ) : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
  have e : Complex.sin w = ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ)
      + ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) * I := by
    conv_lhs => rw [hw]
    rw [Complex.sin_add_mul_I]
    push_cast
    ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  linear_combination (Real.sin w.re) ^ 2 * h1 + (Real.sinh w.im) ^ 2 * h2

theorem norm_sq_cos (w : ℂ) : ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
  have e : Complex.cos w = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ)
      + ((-(Real.sin w.re * Real.sinh w.im) : ℝ) : ℂ) * I := by
    conv_lhs => rw [hw]
    rw [Complex.cos_add_mul_I]
    push_cast
    ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  linear_combination (Real.cos w.re) ^ 2 * h1 + (Real.sinh w.im) ^ 2 * h2

theorem one_le_sinh_sq {y : ℝ} (h : 1 ≤ |y|) : 1 ≤ Real.sinh y ^ 2 := by
  have h1 : |y| ≤ |Real.sinh y| := by
    rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have h2 : 1 ≤ |Real.sinh y| := h.trans h1
  rw [← sq_abs]
  nlinarith

theorem norm_cos_pos {w : ℂ} (h : 1 ≤ |w.im|) : 0 < ‖Complex.cos w‖ := by
  have hc := norm_sq_cos w
  have hsh := one_le_sinh_sq h
  have hpos : 0 < ‖Complex.cos w‖ ^ 2 := by rw [hc]; nlinarith [sq_nonneg (Real.cos w.re)]
  by_contra h0
  have : ‖Complex.cos w‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
  rw [this] at hpos
  norm_num at hpos

theorem norm_tan_le {w : ℂ} (h : 1 ≤ |w.im|) : ‖Complex.tan w‖ ≤ 2 := by
  have hs := norm_sq_sin w
  have hc := norm_sq_cos w
  have hsh := one_le_sinh_sq h
  have hcpos := norm_cos_pos h
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_iff₀ hcpos]
  have h2 : ‖Complex.sin w‖ ^ 2 ≤ (2 * ‖Complex.cos w‖) ^ 2 := by
    rw [mul_pow, hs, hc]
    nlinarith [Real.sin_sq_le_one w.re, sq_nonneg (Real.cos w.re)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

theorem adioso_pt (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves) {t u : ℝ} (ht : 1 ≤ t) (hu : 3 / 2 ≤ u) :
    ‖deriv riemannZeta (((1 - u : ℝ) : ℂ) + t * I) / riemannZeta (((1 - u : ℝ) : ℂ) + t * I)‖
      ≤ 12 + 2 * t + u := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_d2
  set z : ℂ := (u : ℂ) - t * I with hz
  have hzre : z.re = u := by simp [hz]
  have hzim : z.im = -t := by simp [hz]
  have hs : ((1 - u : ℝ) : ℂ) + t * I = 1 - z := by rw [hz]; push_cast; ring
  have hn : ∀ n : ℕ, z ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h
    rw [hzre] at this
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 : z ≠ 1 := fun h ↦ by
    have := congrArg Complex.im h; rw [hzim] at this; simp at this; linarith
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hzre]; linarith)
  have hwim : 1 ≤ |((Real.pi : ℂ) * z / 2).im| := by
    have e : ((Real.pi : ℂ) * z / 2).im = -(Real.pi * t / 2) := by
      rw [show (Real.pi : ℂ) * z / 2 = ((Real.pi / 2 : ℝ) : ℂ) * z by push_cast; ring,
        Complex.im_ofReal_mul, hzim]
      ring
    rw [e, abs_neg, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hcos : Complex.cos ((Real.pi : ℂ) * z / 2) ≠ 0 := norm_pos_iff.mp (norm_cos_pos hwim)
  have hfeq := hfe z hn h1 hζ hcos
  rw [hs]
  have hL1 : deriv riemannZeta (1 - z) / riemannZeta (1 - z)
      = -(deriv riemannZeta z / riemannZeta z) + Complex.log (2 * Real.pi) - Complex.digamma z
        + (Real.pi / 2) * Complex.tan (Real.pi * z / 2) := by
    rw [hfeq]; ring
  rw [hL1]
  have hA := norm_logDeriv_zeta_le_three_halves hv (w := z) (by rw [hzre]; exact hu)
  have hlog : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ 6 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)
    linarith
  have hψ : ‖Complex.digamma z‖ ≤ 2 * t + 1 + u := by
    have ha := GammaSolution.norm_digamma_sub_digamma_re_le (w := z) (by rw [hzre]; linarith)
    rw [hzre, hzim, abs_neg, abs_of_pos (by linarith)] at ha
    have hb := GammaSolution.norm_digamma_sub_log_ofReal_le (x := u) (by linarith)
    have hc : ‖Complex.log (u : ℂ)‖ ≤ u := by
      rw [← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith))]
      have := Real.log_le_sub_one_of_pos (show 0 < u by linarith)
      linarith
    have h2u : t * (2 / u) ≤ 2 * t := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (by rw [div_le_iff₀ (by linarith)]; linarith) (by linarith)
    have h1u : 1 / u ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
    have htri : ‖Complex.digamma z‖ ≤ ‖Complex.digamma z - Complex.digamma ((u : ℝ) : ℂ)‖
        + ‖Complex.digamma ((u : ℝ) : ℂ) - Complex.log ((u : ℝ) : ℂ)‖ + ‖Complex.log (u : ℂ)‖ := by
      have e : Complex.digamma z = (Complex.digamma z - Complex.digamma ((u : ℝ) : ℂ))
        + (Complex.digamma ((u : ℝ) : ℂ) - Complex.log ((u : ℝ) : ℂ)) + Complex.log (u : ℂ) := by ring
      have h5 := norm_add_le ((Complex.digamma z - Complex.digamma ((u : ℝ) : ℂ))
        + (Complex.digamma ((u : ℝ) : ℂ) - Complex.log ((u : ℝ) : ℂ))) (Complex.log (u : ℂ))
      have h6 := norm_add_le (Complex.digamma z - Complex.digamma ((u : ℝ) : ℂ))
        (Complex.digamma ((u : ℝ) : ℂ) - Complex.log ((u : ℝ) : ℂ))
      rw [← e] at h5
      linarith
    linarith
  have htan := norm_tan_le hwim
  have hpi2 : ‖((Real.pi : ℂ) / 2)‖ = Real.pi / 2 := by
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hT4 : ‖(Real.pi / 2 : ℂ) * Complex.tan (Real.pi * z / 2)‖ ≤ Real.pi := by
    rw [norm_mul, hpi2]; nlinarith [norm_nonneg (Complex.tan (Real.pi * z / 2))]
  have h4 := norm_add_le (-(deriv riemannZeta z / riemannZeta z) + Complex.log (2 * Real.pi)
    - Complex.digamma z) ((Real.pi / 2) * Complex.tan (Real.pi * z / 2))
  have h3 := norm_sub_le (-(deriv riemannZeta z / riemannZeta z) + Complex.log (2 * Real.pi))
    (Complex.digamma z)
  have h2 := norm_add_le (-(deriv riemannZeta z / riemannZeta z)) (Complex.log (2 * Real.pi))
  rw [norm_neg] at h2
  linarith

/-! ### Integration against `u e^{-Lu}` -/

theorem integrableOn_pow_exp (k : ℕ) {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun u : ℝ ↦ u ^ k * Real.exp (-(L * u))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := L)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith) one_pos hL
  refine h.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]

theorem integral_pow_exp (k : ℕ) {L : ℝ} (hL : 0 < L) :
    ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-(L * u)) = (k ! : ℝ) / L ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := L) (by positivity) hL
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right] at h
  have e : ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-(L * u))
      = ∫ u in Ioi (0 : ℝ), u ^ (k : ℝ) * Real.exp (-(L * u)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ by simp only [Real.rpow_natCast]
  rw [e, h, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  field_simp
  rw [← mul_pow, one_div, inv_mul_cancel₀ hL.ne', one_pow]

theorem rameauF_nonneg {L η u : ℝ} (hu : 0 ≤ u) : 0 ≤ rameauF L η u := by
  rw [rameauF]; positivity

theorem integrableOn_rameauF {L η : ℝ} (hL : 0 < L) (hη : 0 < η) :
    IntegrableOn (rameauF L η) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_pow_exp 1 hL).const_mul (1 / η))
    (continuous_rameauF hη).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu ↦ ?_)
  have hu0 : (0 : ℝ) < u := hu
  have hden : η ≤ Real.sqrt (η ^ 2 + (1 / 2 - u) ^ 2) := le_sqrt_sq_add_sq_left hη.le
  rw [Real.norm_eq_abs, abs_of_nonneg (rameauF_nonneg hu0.le), rameauF,
    div_le_iff₀ (by positivity), pow_one]
  have hue : 0 ≤ u * Real.exp (-(L * u)) := by positivity
  calc u * Real.exp (-(L * u)) = 1 / η * (u * Real.exp (-(L * u))) * η := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem F_eq_neg {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    CH2ZetaInstance.F s = -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹ := by
  rw [CH2ZetaInstance.F, CH2ZetaInstance.logDeriv_riemannZeta₁_eq hs1 hζ, logDeriv_apply]
  ring

theorem norm_F_le {t u : ℝ} (ht : 0 < t) (hζ : riemannZeta (((1 - u : ℝ) : ℂ) + t * I) ≠ 0) :
    ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖
      ≤ ‖deriv riemannZeta (((1 - u : ℝ) : ℂ) + t * I) / riemannZeta (((1 - u : ℝ) : ℂ) + t * I)‖
        + 1 / t := by
  set s : ℂ := ((1 - u : ℝ) : ℂ) + t * I with hs
  have him : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := fun h ↦ by
    have := congrArg Complex.im h; rw [him] at this; simp at this; linarith
  rw [F_eq_neg hs1 hζ]
  have h1 : ‖(s - 1)⁻¹‖ ≤ 1 / t := by
    rw [norm_inv, ← one_div]
    apply one_div_le_one_div_of_le ht
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, him, Complex.one_im, sub_zero, abs_of_pos ht] at this
    exact this
  have := norm_sub_le (-(deriv riemannZeta s / riemannZeta s)) (s - 1)⁻¹
  rw [norm_neg] at this
  linarith

theorem titchA_nonneg {t : ℝ} (ht : 1000 ≤ t) : 0 ≤ titchA t := by
  have hπ := Real.pi_pos
  have h1 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
  have h2 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  unfold titchA
  positivity

/-- **`lem:saghar` and `lem:adioso`, integrated.** For `t ≥ 1000` at distance at least `Δ` from
every zero ordinate in `(t - 1/4, t + 1/4]`, those zeros on the critical line, and `L ≥ 7`. -/
theorem saghar_integral (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    {t L Δ : ℝ} (ht : 1000 ≤ t) (hL : 7 ≤ L) (hΔ0 : 0 < Δ)
    (hRH : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)), ρ.re = 1 / 2)
    (hfar : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)), Δ ≤ |t - ρ.im|) :
    ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ * Real.exp (-(L * u))
      ≤ titchA t * (1 / (2 * L ^ 2) + 2 / L ^ 3) + 1 / (t * L ^ 2)
        + (∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ)) * (2 / L ^ 2 + 8 / L ^ 3 + 336 / L ^ 4
          + Real.exp (-(L / 2)) * (1 + Real.log (1 / Δ) / 2 + (1 + 2 / L) / (2 * Δ * L)))
        + Real.exp (-(3 / 2 * (L - 1))) * (14 + 2 * t) := by
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < t := by linarith
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := t - 1 / 4) (b := t + 1 / 4) (by linarith)
  have hmem : ∀ ρ ∈ innerZ t,
      ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) := fun ρ hρ ↦
    (Set.Finite.mem_toFinset hfin).mp (by rwa [innerZ_eq hfin] at hρ)
  have hm0 : ∀ ρ ∈ innerZ t, (0 : ℝ) ≤ IEANTN.zetaOrder ρ := fun ρ hρ ↦
    CH2Section7Z.zetaOrder_nonneg_of_mem (fun x hx ↦ show (0 : ℝ) < x by linarith [hx.1]) (hmem ρ hρ)
  have hη : ∀ ρ ∈ innerZ t, Δ ≤ |t - ρ.im| ∧ |t - ρ.im| ≤ Real.exp 1 := by
    intro ρ hρ
    have h := (hmem ρ hρ).2.1
    refine ⟨hfar ρ (hmem ρ hρ), ?_⟩
    have : |t - ρ.im| ≤ 1 / 4 := abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hA0 := titchA_nonneg ht
  have hc0 : 0 ≤ Real.exp (-(3 / 2 * (L - 1))) := (Real.exp_pos _).le
  -- integrability of the majorant's pieces
  have i1 := integrableOn_pow_exp 1 hL0
  have i2 := integrableOn_pow_exp 2 hL0
  have j1 := integrableOn_pow_exp 1 one_pos
  have j2 := integrableOn_pow_exp 2 one_pos
  have iR : IntegrableOn (fun u ↦ ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) * rameauF L |t - ρ.im| u)
      (Ioi 0) :=
    integrable_finsetSum _ fun ρ hρ ↦
      (integrableOn_rameauF hL0 (lt_of_lt_of_le hΔ0 (hη ρ hρ).1)).const_mul _
  have iE : IntegrableOn (fun u ↦ 1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u)))
      (Ioi 0) := (i1.const_mul _).add i2
  have iJ : IntegrableOn (fun u ↦ (12 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) + u ^ 2 * Real.exp (-(1 * u)))
      (Ioi 0) := (j1.const_mul _).add j2
  have iH1 : IntegrableOn (fun u ↦ titchA t * (1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u)))) (Ioi 0) := iE.const_mul _
  have iH2 : IntegrableOn (fun u ↦ 1 / t * (u ^ 1 * Real.exp (-(L * u)))) (Ioi 0) := i1.const_mul _
  have iH4 : IntegrableOn (fun u ↦ Real.exp (-(3 / 2 * (L - 1))) * ((12 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) + u ^ 2 * Real.exp (-(1 * u)))) (Ioi 0) := iJ.const_mul _
  have iS12 : IntegrableOn (fun u ↦ titchA t * (1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u))) + 1 / t * (u ^ 1 * Real.exp (-(L * u)))) (Ioi 0) := iH1.add iH2
  have iS123 : IntegrableOn (fun u ↦ titchA t * (1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u))) + 1 / t * (u ^ 1 * Real.exp (-(L * u))) + ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) * rameauF L |t - ρ.im| u) (Ioi 0) := iS12.add iR
  have iS : IntegrableOn (fun u ↦ titchA t * (1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u))) + 1 / t * (u ^ 1 * Real.exp (-(L * u))) + ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) * rameauF L |t - ρ.im| u + Real.exp (-(3 / 2 * (L - 1))) * ((12 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) + u ^ 2 * Real.exp (-(1 * u)))) (Ioi 0) := iS123.add iH4
  -- the pointwise bound
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ * Real.exp (-(L * u))
        ≤ titchA t * (1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u)))
          + 1 / t * (u ^ 1 * Real.exp (-(L * u)))
          + ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) * rameauF L |t - ρ.im| u
          + Real.exp (-(3 / 2 * (L - 1)))
            * ((12 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) + u ^ 2 * Real.exp (-(1 * u))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have he0 : 0 < Real.exp (-(L * u)) := Real.exp_pos _
    have hsR : 0 ≤ ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) * rameauF L |t - ρ.im| u :=
      Finset.sum_nonneg fun ρ hρ ↦ mul_nonneg (hm0 ρ hρ) (rameauF_nonneg hu0.le)
    have hsim : (((1 - u : ℝ) : ℂ) + t * I).im = t := by simp
    have hsre : (((1 - u : ℝ) : ℂ) + t * I).re = 1 - u := by simp
    rcases le_or_gt u (3 / 2) with hu1 | hu1
    · have hζ : riemannZeta (((1 - u : ℝ) : ℂ) + t * I) ≠ 0 := by
        intro hz
        have hmz : (((1 - u : ℝ) : ℂ) + t * I) ∈
            IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) :=
          ⟨trivial, ⟨by rw [hsim]; linarith, by rw [hsim]; linarith⟩, hz⟩
        have := hfar _ hmz
        rw [hsim, sub_self, abs_zero] at this
        linarith
      have hF := norm_F_le ht0 hζ
      have hP := saghar_pt hH hrvm hsmall hv ht hu0.le hu1 hζ hRH
      have hsum : u * Real.exp (-(L * u)) * ∑ ρ ∈ innerZ t,
            (IEANTN.zetaOrder ρ : ℝ) / Real.sqrt (|t - ρ.im| ^ 2 + (1 / 2 - u) ^ 2)
          = ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) * rameauF L |t - ρ.im| u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ρ _ ↦ by rw [rameauF]; ring
      have h1 : u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ * Real.exp (-(L * u))
          ≤ u * Real.exp (-(L * u)) * ((1 / 2 + u) * titchA t + ∑ ρ ∈ innerZ t,
            (IEANTN.zetaOrder ρ : ℝ) / Real.sqrt (|t - ρ.im| ^ 2 + (1 / 2 - u) ^ 2) + 1 / t) := by
        rw [mul_right_comm]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hc : 0 ≤ Real.exp (-(3 / 2 * (L - 1)))
          * ((12 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) + u ^ 2 * Real.exp (-(1 * u))) := by
        positivity
      have e : u * Real.exp (-(L * u)) * ((1 / 2 + u) * titchA t + ∑ ρ ∈ innerZ t,
            (IEANTN.zetaOrder ρ : ℝ) / Real.sqrt (|t - ρ.im| ^ 2 + (1 / 2 - u) ^ 2) + 1 / t)
          = titchA t * (1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u)))
            + 1 / t * (u ^ 1 * Real.exp (-(L * u)))
            + u * Real.exp (-(L * u)) * ∑ ρ ∈ innerZ t,
              (IEANTN.zetaOrder ρ : ℝ) / Real.sqrt (|t - ρ.im| ^ 2 + (1 / 2 - u) ^ 2) := by ring
      rw [e, hsum] at h1
      linarith
    · have hζ : riemannZeta (((1 - u : ℝ) : ℂ) + t * I) ≠ 0 := by
        refine CH2ZetaInstance.riemannZeta_ne_zero_of_re_neg (by rw [hsre]; linarith) fun n hn ↦ ?_
        have := congrArg Complex.im hn
        rw [hsim] at this
        simp at this
        linarith
      have hF := norm_F_le ht0 hζ
      have hP := adioso_pt hfe hv (t := t) (u := u) (by linarith) hu1.le
      have hexp : Real.exp (-(L * u))
          ≤ Real.exp (-(3 / 2 * (L - 1))) * Real.exp (-(1 * u)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have h1 : u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ * Real.exp (-(L * u))
          ≤ u * (12 + 2 * t + u) * Real.exp (-(L * u)) + 1 / t * (u ^ 1 * Real.exp (-(L * u))) := by
        have : u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ * Real.exp (-(L * u))
            ≤ u * (12 + 2 * t + u + 1 / t) * Real.exp (-(L * u)) := by
          gcongr; linarith
        linarith [show u * (12 + 2 * t + u + 1 / t) * Real.exp (-(L * u))
          = u * (12 + 2 * t + u) * Real.exp (-(L * u)) + 1 / t * (u ^ 1 * Real.exp (-(L * u))) by ring]
      have h2 : u * (12 + 2 * t + u) * Real.exp (-(L * u))
          ≤ Real.exp (-(3 / 2 * (L - 1)))
            * ((12 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) + u ^ 2 * Real.exp (-(1 * u))) := by
        calc u * (12 + 2 * t + u) * Real.exp (-(L * u))
            ≤ u * (12 + 2 * t + u) * (Real.exp (-(3 / 2 * (L - 1))) * Real.exp (-(1 * u))) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ = _ := by ring
      have hA : 0 ≤ titchA t * (1 / 2 * (u ^ 1 * Real.exp (-(L * u))) + u ^ 2 * Real.exp (-(L * u))) := by
        positivity
      linarith
  -- integrate
  have hmono := integral_mono_of_nonneg
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun u ↦ u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ * Real.exp (-(L * u)))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu ↦ by
      have : (0 : ℝ) < u := hu
      show (0 : ℝ) ≤ _
      positivity))
    iS
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt))
  refine hmono.trans ?_
  rw [integral_add iS123 iH4, integral_add iS12 iR, integral_add iH1 iH2,
    integral_const_mul, integral_add (i1.const_mul _) i2, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun ρ hρ ↦
      (integrableOn_rameauF hL0 (lt_of_lt_of_le hΔ0 (hη ρ hρ).1)).const_mul _,
    integral_const_mul, integral_add (j1.const_mul _) j2, integral_const_mul,
    integral_pow_exp 1 hL0, integral_pow_exp 2 hL0, integral_pow_exp 1 one_pos,
    integral_pow_exp 2 one_pos]
  -- the zero terms
  have hR : ∑ ρ ∈ innerZ t, ∫ u in Ioi (0 : ℝ), (IEANTN.zetaOrder ρ : ℝ) * rameauF L |t - ρ.im| u
      ≤ (∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ)) * (2 / L ^ 2 + 8 / L ^ 3 + 336 / L ^ 4
          + Real.exp (-(L / 2)) * (1 + Real.log (1 / Δ) / 2 + (1 + 2 / L) / (2 * Δ * L))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ ↦ ?_
    rw [integral_const_mul]
    obtain ⟨hΔη, hηe⟩ := hη ρ hρ
    have hη0 : 0 < |t - ρ.im| := lt_of_lt_of_le hΔ0 hΔη
    refine mul_le_mul_of_nonneg_left ((rameau hL hη0 hηe).trans ?_) (hm0 ρ hρ)
    have hlog : Real.log (1 / |t - ρ.im|) ≤ Real.log (1 / Δ) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le hΔ0 hΔη)
    have hq : (1 + 2 / L) / (2 * |t - ρ.im| * L) ≤ (1 + 2 / L) / (2 * Δ * L) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have := Real.exp_pos (-(L / 2))
    nlinarith
  simp only [Nat.factorial, Nat.cast_one, one_pow, div_one, Nat.succ_eq_add_one,
    zero_add, mul_one] at *
  have e1 : titchA t * (1 / 2 * (1 / L ^ 2) + 2 / L ^ 3) = titchA t * (1 / (2 * L ^ 2) + 2 / L ^ 3) := by
    field_simp
  have e2 : 1 / t * (1 / L ^ 2) = 1 / (t * L ^ 2) := by field_simp
  nlinarith

end CH2Section81
