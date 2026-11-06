/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import RS12.Proof

/-! The elementary upper bound in Rosser--Schoenfeld (1962), Theorem 25.
The already proved Theorem 12 has a stronger linear coefficient, so this
result needs no new numerical certificate or zero-free-region hypothesis. -/
namespace RS5Historical
open Real Chebyshev

/-- The constant `a` in RS1962 Theorem 25. -/
noncomputable def theorem25Constant : ℝ :=
  (7 / 15) * log 2 + (3 / 10) * log 3 + (1 / 6) * log 5

/-- Rational lower bound sufficient to compare Theorems 12 and 25. -/
theorem theorem25_constant_lower : (47 / 54 : ℝ) ≤ theorem25Constant := by
  have h2 : (2 / 3 : ℝ) ≤ log 2 := by
    convert le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) using 1 <;> norm_num
  have h3 : (1 : ℝ) ≤ log 3 := by
    convert le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> norm_num
  have h54 : (2 / 9 : ℝ) ≤ log (5 / 4 : ℝ) := by
    convert le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) using 1 <;> norm_num
  have he : log (5 : ℝ) = log (5 / 4 : ℝ) + 2 * log 2 := by
    calc
      log (5 : ℝ) = log ((5 / 4 : ℝ) * 2 ^ 2) := by norm_num
      _ = _ := by rw [log_mul (by norm_num) (by norm_num), log_pow]; norm_num
  unfold theorem25Constant
  linarith

/-- The proved RS12 coefficient is strictly smaller than the T25 coefficient. -/
theorem theorem25_coefficient_gt_rs12 : RS_prime.c₀ < (6 / 5) * theorem25Constant := by
  have h := theorem25_constant_lower
  norm_num [RS_prime.c₀]
  linarith

/-- RS1962 Theorem 25, including its explicit elementary correction. -/
theorem theorem25 {x : ℝ} (hx : 1 ≤ x) :
    θ x ≤ ψ x ∧
      ψ x < (6 / 5) * theorem25Constant * x + (3 * log x + 5) * (log x + 1) := by
  refine ⟨theta_le_psi x, ?_⟩
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl : 0 ≤ log x := log_nonneg hx
  have hc : 0 ≤ (3 * log x + 5) * (log x + 1) := by positivity
  exact (RS_prime.theorem_12 hp).trans_le
    ((mul_le_mul_of_nonneg_right theorem25_coefficient_gt_rs12.le hp.le).trans
      (le_add_of_nonneg_right hc))

end RS5Historical
