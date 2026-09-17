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

end CH2Section81
