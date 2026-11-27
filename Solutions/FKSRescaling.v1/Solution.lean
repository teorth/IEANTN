/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import IEANTN.Nodes.FKSRescaling.v1.Conclusions

/-!
# Solution: `FKSRescaling.v1`

With `R = 5.5666305`, `2.3593707 ≤ √R ≤ 2.3593708`, both by squaring. Then

* `R^{3/2} = R √R`, so `9.22022 R^{3/2} ≥ 9.22022 · R · 2.3593707 = 121.0960174… > 121.096`;
* `0.8476836 √R ≤ 0.8476836 · 2.3593708 = 1.99999993… < 2`.

Does not import the challenge module: Comparator compares two modules declaring the same names.
-/

open Real

private lemma sqrt_R_lower : (2.3593707 : ℝ) ≤ √(5.5666305 : ℝ) :=
  Real.le_sqrt_of_sq_le (by norm_num)

private lemma sqrt_R_upper : √(5.5666305 : ℝ) ≤ 2.3593708 :=
  (Real.sqrt_le_left (by norm_num)).2 (by norm_num)

private lemma rpow_three_halves :
    (5.5666305 : ℝ) ^ ((3 : ℝ) / 2) = 5.5666305 * √(5.5666305 : ℝ) := by
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, rpow_add (by norm_num), rpow_one,
    sqrt_eq_rpow]

theorem FKSRescaling.v1.challenge_rescaled_A_exceeds_printed :
    FKSRescaling.v1.rescaled_A_exceeds_printed := by
  unfold FKSRescaling.v1.rescaled_A_exceeds_printed
  rw [rpow_three_halves]
  have h := mul_le_mul_of_nonneg_left sqrt_R_lower
    (by norm_num : (0 : ℝ) ≤ 9.22022 * 5.5666305)
  nlinarith [h]

theorem FKSRescaling.v1.challenge_rescaled_C_is_short_of_two :
    FKSRescaling.v1.rescaled_C_is_short_of_two := by
  unfold FKSRescaling.v1.rescaled_C_is_short_of_two
  have h := mul_le_mul_of_nonneg_left sqrt_R_upper (by norm_num : (0 : ℝ) ≤ 0.8476836)
  nlinarith [h]
