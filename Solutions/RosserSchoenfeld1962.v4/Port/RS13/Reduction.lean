/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Port.PrimePowers
import Mathlib.Data.Num.Prime

namespace RS5Historical.Theorem13
open Real Chebyshev Finset ArithmeticFunction

/-- A convenient exact threshold; the stronger coefficient leaves room below
both the historical decimal and the value of the quotient at 361. -/
theorem gap_large {x : ℝ} (hx : 46656 ≤ x) :
    ψ x - θ x < (7 / 5) * sqrt x := by
  have hp : 0 < x := by linarith
  have h6 : (6 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
    calc
      (6 : ℝ) = (46656 : ℝ) ^ (1 / 6 : ℝ) := by
        rw [show (46656 : ℝ) = 6 ^ 6 by norm_num,
          ← rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 6)]
        norm_num
      _ ≤ _ := rpow_le_rpow (by norm_num) hx (by norm_num)
  have he : x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) = sqrt x := by
    rw [← rpow_add hp, show (1 / 3 : ℝ) + 1 / 6 = 1 / 2 by norm_num,
      ← sqrt_eq_rpow]
  have hr : 6 * x ^ (1 / 3 : ℝ) ≤ sqrt x := by
    have h := mul_le_mul_of_nonneg_left h6 (rpow_nonneg hp.le (1 / 3 : ℝ))
    rw [he] at h
    linarith
  have h := psi_sub_theta_le_prime_powers (show 1 ≤ x by linarith)
  rw [← sqrt_eq_rpow] at h
  have hs := sqrt_pos.2 hp
  nlinarith

end RS5Historical.Theorem13
