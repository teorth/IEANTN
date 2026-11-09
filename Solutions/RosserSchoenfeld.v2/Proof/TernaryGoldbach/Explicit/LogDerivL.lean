import TernaryGoldbach.Explicit.LGrowthLeft
import TernaryGoldbach.Explicit.ZeroCount
import TernaryGoldbach.Explicit.Landau

/-!
# `L'/L(z, χ)` near height `T`: Landau's lemma for `L(s, χ)`

For `χ` primitive, `χ ≠ 1`, `T ∈ ℝ`, `c = 2 + iT`: `|L| ≤ B_T` on `|z − c| ≤ 10`, with
`B_T = 512 q⁹ (q + 1)(|T| + 22) e^{π(|T|+10)/2}` (`LGrowth` for `ℜz ≥ 1/4`, `LGrowthLeft` for
`ℜz ≤ 1/4`), and `|L(c)| ≥ 0.355`. Hence, for `|z − c| ≤ 5/2` (`ℜz ∈ [−1/2, 9/2]` on the line
`ℑz = T`), `|L'/L(z) − Σ_{|ρ − c| < 5} m_ρ/(z − ρ)| ≤ 4.8 log(B_T/0.355)`, and there are at most
`log(B_T/0.355)/log 2` zeros in `|ρ − c| ≤ 5`.
-/

open Complex Metric Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

/-- `B_T = 512 q⁹ (q + 1)(|T| + 22) e^{π(|T|+10)/2}`. -/
noncomputable def BT (N : ℕ) (T : ℝ) : ℝ :=
  512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) * Real.exp (π * (|T| + 10) / 2)

theorem one_le_BT {N : ℕ} [NeZero N] (T : ℝ) : 512 ≤ BT N T := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h9 : (1:ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ hN1
  have he : (1:ℝ) ≤ Real.exp (π * (|T| + 10) / 2) := Real.one_le_exp (by positivity)
  unfold BT
  have : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) * Real.exp (π * (|T| + 10) / 2) := by
    have h1 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by nlinarith
    have h2 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) := by nlinarith [abs_nonneg T]
    nlinarith
  nlinarith

theorem norm_L_le_BT {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T : ℝ} {w : ℂ} (hw : w ∈ closedBall (2 + T * I) 10) :
    ‖χ.LFunction w‖ ≤ BT N T := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
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
  have he1 : Real.exp (π * |w.im| / 2) ≤ Real.exp (π * (|T| + 10) / 2) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hwim1 Real.pi_pos.le; linarith
  rcases le_total w.re (1 / 4) with h | h
  · refine (norm_LFunction_left hχ hχ1 hre1 h).trans ?_
    unfold BT
    have h1 : |w.im| + 9 ≤ |T| + 22 := by linarith
    have hA : 0 ≤ 512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) he1 (by positivity) (by positivity)
  · refine (norm_LFunction_le hχ1 (by linarith)).trans ?_
    have hwn : ‖w‖ ≤ |T| + 22 := by
      refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
      rw [abs_of_pos (by linarith : (0:ℝ) < w.re)]; linarith
    have h4 : ((N : ℝ) + 1) * ‖w‖ / w.re ≤ 4 * ((N : ℝ) + 1) * (|T| + 22) := by
      rw [div_le_iff₀ (by linarith)]
      have hp : 0 ≤ 4 * ((N : ℝ) + 1) * (|T| + 22) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hwn (by positivity : (0:ℝ) ≤ (N : ℝ) + 1)
      have h2 := mul_le_mul_of_nonneg_left h hp
      nlinarith
    refine h4.trans ?_
    have h9 : (1:ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ hN1
    have he : (1:ℝ) ≤ Real.exp (π * (|T| + 10) / 2) := Real.one_le_exp (by positivity)
    unfold BT
    have hp : 0 ≤ ((N : ℝ) + 1) * (|T| + 22) := by positivity
    calc 4 * ((N : ℝ) + 1) * (|T| + 22) = 4 * (((N : ℝ) + 1) * (|T| + 22)) := by ring
      _ ≤ 512 * (N : ℝ) ^ 9 * (((N : ℝ) + 1) * (|T| + 22)) * Real.exp (π * (|T| + 10) / 2) := by
        have : (4:ℝ) ≤ 512 * (N : ℝ) ^ 9 * Real.exp (π * (|T| + 10) / 2) := by nlinarith
        nlinarith
      _ = _ := by ring

theorem norm_LFunction_two_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.re = 2) : ‖χ.LFunction s‖ ≤ π ^ 2 / 6 := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by rw [hs]; norm_num), LSeries]
  refine tsum_of_norm_bounded hasSum_zeta_two fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · simp [h0]
  · rw [hs, Real.rpow_two]
    exact div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)

theorem norm_L_center_ge {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    0.355 ≤ ‖χ.LFunction (2 + T * I)‖ := by
  have h := norm_LFunction_two_ge χ (s := 2 + T * I) (by simp)
  have hpi := Real.pi_lt_d4
  nlinarith [Real.pi_pos]

/-- **Landau for `L(s, χ)`** at `c = 2 + iT`, `R = 10`. -/
theorem logDeriv_L_near {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T : ℝ} {z : ℂ} (hz : z ∈ closedBall (2 + T * I) (10 / 4))
    (hLz : χ.LFunction z ≠ 0) :
    ‖logDeriv χ.LFunction z - ∑ u ∈ zerosIn χ.LFunction (2 + T * I) 10 (10 / 2),
        ((divB χ.LFunction (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ ≤
      4.8 * Real.log (BT N T / 0.355) := by
  have hc := norm_L_center_ge χ T
  have hc0 : χ.LFunction (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := one_le_BT (N := N) T
  have hcB : ‖χ.LFunction (2 + T * I)‖ < BT N T := by
    have := norm_LFunction_two_le χ (s := 2 + T * I) (by simp)
    have hpi := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have h := landau (DirichletCharacter.differentiable_LFunction hχ1) hc0 (by norm_num : (0:ℝ) < 10)
    (fun w hw => norm_L_le_BT hχ hχ1 hw) hcB hz hLz
  refine h.trans ?_
  have hpos : 0 < BT N T / ‖χ.LFunction (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (BT N T / ‖χ.LFunction (2 + T * I)‖) ≤ Real.log (BT N T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  calc 48 * Real.log (BT N T / ‖χ.LFunction (2 + T * I)‖) / 10
      = 4.8 * Real.log (BT N T / ‖χ.LFunction (2 + T * I)‖) := by ring
    _ ≤ 4.8 * Real.log (BT N T / 0.355) := by gcongr

/-- **Zero count** in `|ρ − (2 + iT)| ≤ 5`: at most `log(B_T/0.355)/log 2`. -/
theorem zero_count_5 {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (T : ℝ) :
    ((∑ᶠ u, MeromorphicOn.divisor χ.LFunction (closedBall (2 + T * I) |(5 : ℝ)|) u : ℤ) : ℝ) ≤
      Real.log (BT N T / 0.355) / Real.log 2 := by
  have hc := norm_L_center_ge χ T
  have hc0 : χ.LFunction (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := one_le_BT (N := N) T
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall (2 + T * I) |(10 : ℝ)|) := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z
  have h := hf.sum_divisor_le (r := 5) (R := 10) (by norm_num) (by norm_num) (by linarith) hc0
    (fun w hw => norm_L_le_BT hχ hχ1 (sphere_subset_closedBall (by
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 10)] at hw)))
  refine h.trans ?_
  have hpos : 0 < BT N T / ‖χ.LFunction (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (BT N T / ‖χ.LFunction (2 + T * I)‖) ≤ Real.log (BT N T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  rw [show (10:ℝ) / 5 = 2 by norm_num]
  exact div_le_div_of_nonneg_right hle (Real.log_nonneg (by norm_num))

end TernaryGoldbach.Explicit
