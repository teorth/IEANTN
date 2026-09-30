/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.Constants

open Real Chebyshev
namespace RS12Factorial

/-- An anchored logarithm bound for the elementary recurrence cutoff. -/
private theorem factorial_log_bound {x : ℝ} (hx : 500000 ≤ x) :
    log x ≤ 14 * x / 500000 := by
  have hp : 0 < x := by linarith
  have hbase : log (500000 : ℝ) ≤ 14 := by
    have he : (500000 : ℝ) = 2^5 * 5^6 := by norm_num
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
    linarith [kernel_log_two, kernel_log_five]
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 500000 by positivity)
  rw [Real.log_div hp.ne' (by norm_num)] at h
  linarith

/-- The fully quantified factorial majorant needed above 500000. -/
theorem factorial_upper {x : ℝ} (hx : 500000 ≤ x) :
    (realWeights factorialWeights).sum (fun m b => b * T (x / m)) ≤ 1.021 * x := by
  have hp : 0 < x := by linarith
  have hlog : 0 ≤ log x := Real.log_nonneg (by linarith)
  have h := weighted_T_upper factorialWeights (by linarith : 1 ≤ x)
    (fun dw hd => ⟨(factorial_weights_bounds dw hd).1,
      (by have hb : (dw.1 : ℝ) ≤ 360360 := by exact_mod_cast (factorial_weights_bounds dw hd).2
          linarith)⟩) factorial_balance_real
  have hs : (weightSum factorialWeights : ℝ) ≤ 0 := by
    exact_mod_cast factorial_weight_sum_nonpos
  have ha : (weightAbsSum factorialWeights : ℝ) ≤ 170000000 := by
    exact_mod_cast factorial_weight_abs_sum_le
  have hc := mul_le_mul_of_nonneg_right factorial_slope_le hp.le
  have hl := mul_le_mul_of_nonneg_right ha hlog
  have hxlog := factorial_log_bound hx
  nlinarith

end RS12Factorial
