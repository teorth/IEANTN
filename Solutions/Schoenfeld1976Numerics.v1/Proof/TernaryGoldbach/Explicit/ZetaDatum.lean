import TernaryGoldbach.Explicit.ZetaGrowth

/-!
# `(s − 1)ζ(s)` is an `LDatum`

`B_ζ(T) = 4·10⁵ (|T| + 22)³ e^{π(|T|+10)/2}`, `D = 2`, `C_R = C₃ + 2`. The values of `ζ` on `ℜs = 2` and
`ζ'/ζ` on `ℜs = 3/2` come from the `L(s, χ)` lemmas for the trivial character mod `1`
(`LFunction_modOne_eq`).
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real Topology

namespace TernaryGoldbach.Explicit

/-- `B_ζ(T)`. -/
noncomputable def Bz (T : ℝ) : ℝ := 4e5 * (|T| + 22) ^ 3 * Real.exp (π * (|T| + 10) / 2)

theorem Bz_ge (T : ℝ) : 4e5 * (|T| + 22) ^ 3 ≤ Bz T := by
  unfold Bz
  have : 1 ≤ Real.exp (π * (|T| + 10) / 2) := Real.one_le_exp (by positivity)
  have h0 : 0 ≤ 4e5 * (|T| + 22) ^ 3 := by positivity
  nlinarith

theorem one_le_Bz (T : ℝ) : 1 ≤ Bz T := by
  have := Bz_ge T
  have h : (1:ℝ) ≤ 4e5 * (|T| + 22) ^ 3 := by
    have : (22:ℝ) ^ 3 ≤ (|T| + 22) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith [abs_nonneg T]) 3
    nlinarith
  linarith

theorem Bz_mono {T T' : ℝ} (h : |T| ≤ |T'|) : Bz T ≤ Bz T' := by
  unfold Bz
  have h1 : (|T| + 22) ^ 3 ≤ (|T'| + 22) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : Real.exp (π * (|T| + 10) / 2) ≤ Real.exp (π * (|T'| + 10) / 2) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity) (by positivity)

theorem norm_zetaF_le_Bz (T : ℝ) {w : ℂ} (hw : w ∈ closedBall (2 + T * I) 10) :
    ‖zetaF w‖ ≤ Bz T := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := Complex.abs_re_le_norm (w - (2 + T * I))
  have him := Complex.abs_im_le_norm (w - (2 + T * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im,
    Complex.add_im, Complex.im_ofNat, Complex.mul_im, zero_add, add_zero] at hre him
  have hwim1 : |w.im| ≤ |T| + 10 := by
    have := abs_sub_abs_le_abs_sub w.im T; linarith [abs_sub_comm w.im T]
  have hre1 : -8 ≤ w.re := by linarith [neg_abs_le (w.re - 2)]
  have hre2 : w.re ≤ 12 := by linarith [le_abs_self (w.re - 2)]
  have hT0 := abs_nonneg T
  have hwn : ‖w‖ ≤ |T| + 22 := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    have : |w.re| ≤ 12 := abs_le.2 ⟨by linarith, hre2⟩
    linarith
  have hw1 : ‖w - 1‖ ≤ |T| + 22 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have : |(w - 1).re| ≤ 11 := by simp; rw [abs_le]; constructor <;> linarith
    have h2 : |(w - 1).im| = |w.im| := by simp
    linarith
  have h1w : ‖1 - w‖ ≤ |T| + 22 := by rw [norm_sub_rev]; exact hw1
  have hB := Bz_ge T
  rcases le_total w.re (1 / 4) with h | h
  · refine (norm_zetaF_left hre1 h).trans ?_
    have hR : 3 / 4 ≤ 1 - w.re := by linarith
    have hX : ‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re) ≤ 1.38 * (|T| + 22) ^ 2 := by
      have h3 : ‖1 - w‖ * ‖w‖ / (1 - w.re) ≤ (|T| + 22) * (|T| + 22) / (3 / 4) := by
        apply div_le_div₀ (by positivity) (mul_le_mul h1w hwn (norm_nonneg _) (by positivity))
          (by norm_num) hR
      nlinarith
    have hE : Real.exp (π * |w.im| / 2) ≤ Real.exp (π * (|T| + 10) / 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    have hpi := Real.pi_lt_d4
    calc 1.18 * π * 40320 * ‖w - 1‖ * Real.exp (π * |w.im| / 2) *
          (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re))
        ≤ 1.18 * 3.1416 * 40320 * (|T| + 22) * Real.exp (π * (|T| + 10) / 2) *
          (1.38 * (|T| + 22) ^ 2) := by gcongr
      _ ≤ Bz T := by
          unfold Bz
          have hE0 := Real.exp_pos (π * (|T| + 10) / 2)
          have : (1.18 * 3.1416 * 40320 * 1.38 : ℝ) ≤ 4e5 := by norm_num
          have hx : 0 ≤ (|T| + 22) ^ 3 * Real.exp (π * (|T| + 10) / 2) := by positivity
          calc 1.18 * 3.1416 * 40320 * (|T| + 22) * Real.exp (π * (|T| + 10) / 2) *
                (1.38 * (|T| + 22) ^ 2)
              = (1.18 * 3.1416 * 40320 * 1.38) * ((|T| + 22) ^ 3 * Real.exp (π * (|T| + 10) / 2)) := by
                ring
            _ ≤ 4e5 * ((|T| + 22) ^ 3 * Real.exp (π * (|T| + 10) / 2)) :=
                mul_le_mul_of_nonneg_right this hx
            _ = _ := by ring
  · refine (norm_zetaF_le (by linarith)).trans ?_
    have h3 : ‖w‖ * ‖w - 1‖ / w.re ≤ (|T| + 22) * (|T| + 22) / (1 / 4) :=
      div_le_div₀ (by positivity) (mul_le_mul hwn hw1 (norm_nonneg _) (by positivity)) (by norm_num) h
    have : ‖w‖ + ‖w‖ * ‖w - 1‖ / w.re ≤ 5 * (|T| + 22) ^ 2 := by nlinarith
    refine this.trans ?_
    have : 5 * (|T| + 22) ^ 2 ≤ 4e5 * (|T| + 22) ^ 3 := by
      have h22 : (22:ℝ) ≤ |T| + 22 := by linarith
      nlinarith [sq_nonneg (|T| + 22)]
    linarith

/-! ## `ζ` on `ℜs = 2` and `ζ'/ζ` on `ℜs = 3/2` via the trivial character -/

theorem LFunction_one_mod_one : (1 : DirichletCharacter ℂ 1).LFunction = riemannZeta :=
  DirichletCharacter.LFunction_modOne_eq

theorem norm_zeta_two_ge {s : ℂ} (hs : s.re = 2) : 2 - π ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have := norm_LFunction_two_ge (1 : DirichletCharacter ℂ 1) hs
  rwa [LFunction_one_mod_one] at this

theorem norm_zeta_two_le {s : ℂ} (hs : s.re = 2) : ‖riemannZeta s‖ ≤ π ^ 2 / 6 := by
  have := norm_LFunction_two_le (1 : DirichletCharacter ℂ 1) hs
  rwa [LFunction_one_mod_one] at this

theorem norm_logDeriv_zeta_right (y : ℝ) :
    ‖logDeriv riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ C3 := by
  have := norm_logDeriv_L_right (1 : DirichletCharacter ℂ 1) y
  rwa [LFunction_one_mod_one] at this

theorem zetaF_center_ge (T : ℝ) : 0.355 ≤ ‖zetaF (2 + T * I)‖ := by
  have hne : (2 : ℂ) + T * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [zetaF_of_ne hne, norm_mul]
  have h1 : 1 ≤ ‖(2 : ℂ) + T * I - 1‖ := by
    have := Complex.abs_re_le_norm ((2 : ℂ) + T * I - 1)
    simp at this; norm_num at this; linarith
  have h2 := norm_zeta_two_ge (s := 2 + T * I) (by simp)
  have hpi := Real.pi_lt_d4
  have h3 : (0.355 : ℝ) ≤ 2 - π ^ 2 / 6 := by nlinarith [Real.pi_pos]
  nlinarith [norm_nonneg (riemannZeta (2 + T * I))]

theorem zetaF_center_lt (T : ℝ) : ‖zetaF (2 + T * I)‖ < Bz T := by
  have hne : (2 : ℂ) + T * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [zetaF_of_ne hne, norm_mul]
  have h1 : ‖(2 : ℂ) + T * I - 1‖ ≤ 1 + |T| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp; norm_num
  have h2 := norm_zeta_two_le (s := 2 + T * I) (by simp)
  have hpi := Real.pi_lt_d4
  have h3 : π ^ 2 / 6 ≤ 1.65 := by nlinarith [Real.pi_pos]
  have hB := Bz_ge T
  have hT0 := abs_nonneg T
  have h4 : (1 + |T|) * 1.65 < 4e5 * (|T| + 22) ^ 3 := by nlinarith [sq_nonneg (|T| + 22)]
  calc ‖(2 : ℂ) + T * I - 1‖ * ‖riemannZeta (2 + T * I)‖ ≤ (1 + |T|) * 1.65 :=
        mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
    _ < _ := by linarith

theorem log_Bz_le (T : ℝ) : Real.log (Bz T / 0.355) ≤ 2 + 37 + 2.6 * |T| := by
  have hT0 := abs_nonneg T
  have e : Bz T / 0.355 = (4e5 / 0.355) * (|T| + 22) ^ 3 * Real.exp (π * (|T| + 10) / 2) := by
    unfold Bz; ring
  rw [e, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by norm_num) (by positivity),
    Real.log_exp, Real.log_pow]
  have h1 : Real.log (4e5 / 0.355) ≤ 13.94 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e13 : Real.exp 13.94 = Real.exp 1 ^ 13 * Real.exp 0.94 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h094 : 2.5588 ≤ Real.exp 0.94 := by
      have := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.94) 6
      norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢; linarith
    rw [e13]
    have : (2.7182818283 : ℝ) ^ 13 ≤ Real.exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) h.le 13
    nlinarith [pow_pos (Real.exp_pos 1) 13]
  have h2 : Real.log (|T| + 22) ≤ Real.log 22 + |T| / 22 := by
    have : Real.log (|T| + 22) - Real.log 22 ≤ |T| / 22 := by
      rw [← Real.log_div (by positivity) (by norm_num)]
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (|T| + 22) / 22 by positivity)
      linarith [show (|T| + 22) / 22 - 1 = |T| / 22 by ring]
    linarith
  have h22 : Real.log 22 ≤ 3.0911 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e3 : Real.exp 3.0911 = Real.exp 1 ^ 3 * Real.exp 0.0911 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h09 : 1.09537 ≤ Real.exp 0.0911 := by
      have := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.0911) 4
      norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢; linarith
    rw [e3]
    have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
    nlinarith [pow_pos (Real.exp_pos 1) 3]
  have hpi := Real.pi_lt_d4
  push_cast
  nlinarith

theorem zetaF_ne_zero_right {s : ℂ} (hs : 1 < s.re) : zetaF s ≠ 0 := by
  have hne : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [zetaF_of_ne hne]
  exact mul_ne_zero (sub_ne_zero.2 hne) (riemannZeta_ne_zero_of_one_lt_re hs)

theorem zetaF_ne_zero_strip {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 0) : zetaF s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at h2; simp at h2
  have hs1 : s ≠ 1 := by intro h; rw [h] at h2; simp at h2; linarith
  rw [zetaF_left_eq hs0 (by linarith)]
  have hre1 : (1 - s).re = 1 - s.re := by simp
  refine mul_ne_zero (sub_ne_zero.2 hs1) (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    two_ne_zero ?_) ?_) ?_) (div_ne_zero (zetaF_ne_zero_right (by rw [hre1]; linarith)) (neg_ne_zero.2 hs0)))
  · rw [Complex.cpow_ne_zero_iff]; left
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  · apply Complex.Gamma_ne_zero
    intro m hm
    have := congrArg Complex.re hm
    rw [hre1] at this; simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have h := congrArg Complex.re hk
    simp at h
    -- `π s.re / 2 = k π`, so `s.re = 2k`
    have hk' : s.re = 2 * k := by
      have hp := Real.pi_pos
      field_simp at h
      nlinarith
    have hk1 : (k : ℝ) < 0 := by linarith
    have hk2 : -1 / 2 < (k : ℝ) := by linarith
    have : k < 0 := by exact_mod_cast hk1
    have : -1 < k := by
      have : (-1 : ℝ) < k := by linarith
      exact_mod_cast this
    omega

theorem logDeriv_zetaF_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv zetaF s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hev : zetaF =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht using zetaF_of_ne ht
  have hd : deriv zetaF s = 1 * riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [hev.deriv_eq]
    exact ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt |>.deriv
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [logDeriv_apply, logDeriv_apply, hd, zetaF_of_ne hs]
  field_simp

theorem norm_logDeriv_zetaF_right (y : ℝ) :
    ‖logDeriv zetaF (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ C3 + 2 := by
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) + y * I with hs
  have hsre : s.re = 3 / 2 := by simp [hs]
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre; norm_num at hsre
  rw [logDeriv_zetaF_eq hs1 (riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; norm_num))]
  have h1 : ‖1 / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hs1))]
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre] at this
    norm_num at this ⊢; linarith
  have h2 := norm_logDeriv_zeta_right y
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **`(s − 1)ζ(s)` is an `LDatum`.** -/
theorem ldatum_zeta : LDatum zetaF Bz 2 (C3 + 2) where
  diff := differentiable_zetaF
  center_ge := zetaF_center_ge
  center_lt := zetaF_center_lt
  bound := fun T w hw => norm_zetaF_le_Bz T hw
  B_ge := one_le_Bz
  B_mono := fun T T' h => Bz_mono h
  logB_lin := log_Bz_le
  D_nonneg := by norm_num
  nz_strip := fun s h1 h2 => zetaF_ne_zero_strip h1 h2
  nz_right := fun s h => zetaF_ne_zero_right h
  right_bound := norm_logDeriv_zetaF_right

end TernaryGoldbach.Explicit
