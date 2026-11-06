/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Interval.Lower
import Interval.Counting
import RS12.Proof

/-!
For `x ≥ 4096`, write `s = sqrt x ≥ 64`. Costa–Pereira and the proved v1
upper bound give `psi(2x)-theta(2x) < (19/4)s ≤ (19/256)x`.
The last inequality is the reason for choosing the convenient square cutoff `64²`;
no claim that it is optimal is made. Also `5 log(2x)+1 < x/50`.
Consequently the theta difference exceeds
`(1.84 - 1.03883 - 19/256 - 1/50)x = 0.70695125x`,
which exceeds the `0.7x` used below by `5561x/800000` (28.47232 at 4096).
At 4096 the weighted target is exactly `0.65x`, leaving another `0.05x`
against `0.7x`. All comparisons below are proved with exact real arithmetic.
-/

namespace RSInterval
open Real

lemma log_two_mul_bound {x : ℝ} (hx : 4096 ≤ x) :
    log (2*x) ≤ (5/32 : ℝ) * sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs : 64 ≤ sqrt x := by
    apply (le_sqrt (by norm_num) hx0.le).mpr
    norm_num; exact hx
  have hs0 : 0 < sqrt x := by linarith
  have hl := log_le_sub_one_of_pos (div_pos hs0 (by norm_num : (0:ℝ)<64))
  have he : log (2*x) = 13 * log 2 + 2 * log (sqrt x / 64) := by
    rw [log_div hs0.ne' (by norm_num), log_mul (by norm_num) hx0.ne']
    have h64 : log (64 : ℝ) = 6 * log 2 := by
      rw [show (64 : ℝ) = 2^6 by norm_num, log_pow]; norm_num
    rw [h64, log_sqrt hx0.le]
    ring
  rw [he]
  have h2 := log_two_lt_d9
  nlinarith

lemma tail (x : ℝ) (hx : 4096 ≤ x) :
    3*x/(5*log x) < IEANTN.primeCounting (2*x) - IEANTN.primeCounting x := by
  have hx0 : 0 < x := by linarith
  have hL : 8 < log x := by
    have h := log_le_log (by norm_num : (0:ℝ)<4096) hx
    have he : log (4096 : ℝ) = 12 * log 2 := by
      rw [show (4096 : ℝ) = 2^12 by norm_num, log_pow]; norm_num
    rw [he] at h
    linarith [log_two_gt_d9]
  have hs : 64 ≤ sqrt x := by
    apply (le_sqrt (by norm_num) hx0.le).mpr
    norm_num; exact hx
  have hs0 : 0 ≤ sqrt x := sqrt_nonneg _
  have hs2 : sqrt x ^ 2 = x := sq_sqrt hx0.le
  have hy2 : sqrt (2*x) ^ 2 = 2*x := sq_sqrt (by positivity)
  have hsy : sqrt (2*x) ≤ (3/2 : ℝ)*sqrt x := by
    nlinarith [sqrt_nonneg (2*x)]
  have hl := log_two_mul_bound hx
  have hl0 : 0 ≤ log (2*x) := log_nonneg (by linarith)
  have hterm (n : ℝ) (hn : n⁻¹ ≤ 1/2) :
      Chebyshev.psi ((2*x)^n⁻¹) < 1.03883 * sqrt (2*x) := by
    have h := RS_prime.theorem_12 (rpow_pos_of_pos (by positivity : 0 < 2*x) n⁻¹)
    dsimp [RS_prime.c₀] at h
    have hr : (2*x)^n⁻¹ ≤ sqrt (2*x) := by
      rw [sqrt_eq_rpow]
      exact rpow_le_rpow_of_exponent_le (by linarith) hn
    nlinarith
  have htheta := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (2*x)
  have herror : Chebyshev.psi (2*x) - Chebyshev.theta (2*x) < (19/256 : ℝ)*x := by
    have h2 := hterm 2 (by norm_num)
    have h3 := hterm 3 (by norm_num)
    have h5 := hterm 5 (by norm_num)
    have hsq : 64*sqrt x ≤ x := by nlinarith
    nlinarith
  have hsmall : 5*log (2*x) + 1 < (1/50 : ℝ)*x := by
    have hsq : 64 * sqrt x ≤ x := by nlinarith
    nlinarith
  have hlow := Chebyshev.psi_lower_elementary (2*x) (by linarith)
  have hupp := RS_prime.theorem_12 (x := x) hx0
  dsimp [RS_prime.c₀] at hupp
  have htheta2 := Chebyshev.theta_le_psi x
  have hd : (7/10 : ℝ)*x < Chebyshev.theta (2*x) - Chebyshev.theta x := by
    nlinarith
  have hcount := theta_sub_le hx0.le (show x ≤ 2*x by linarith)
  have hlog : log (2*x) = log 2 + log x := log_mul (by norm_num) hx0.ne'
  have hcmp : (3*x/(5*log x))*log (2*x) < (7/10 : ℝ)*x := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < 5*log x), hlog]
    have h2 := log_two_lt_d9
    nlinarith [mul_pos hx0 (show 0 < log x - 8 by linarith)]
  exact (mul_lt_mul_iff_left₀ (log_pos (by linarith : 1 < 2*x))).mp
    (hcmp.trans (hd.trans_le hcount))

end RSInterval
