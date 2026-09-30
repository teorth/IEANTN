/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.FactorialData
import RS12.FactorialUpper

open Real Chebyshev
namespace RS12Factorial

/-- The certified periodic floor kernel is nonnegative on the whole real line. -/
private theorem factorial_E_nonneg (y : ℝ) : 0 ≤ E (realWeights factorialWeights) y := by
  rw [E_realWeights, floorNumerator_mod_period factorialWeights (by norm_num : 0 < 360360)
    factorial_weights_divisors factorial_floor_balance]
  have hb := factorial_period_bound (Nat.mod_lt ⌊y⌋₊ (by norm_num : 0 < 360360))
  have hn : 0 ≤ floorNumerator factorialWeights (⌊y⌋₊ % 360360) := by
    split_ifs at hb <;> linarith
  exact div_nonneg (by exact_mod_cast hn) (by norm_num)

/-- The first multiplicative interval has floor-kernel weight at least one. -/
private theorem factorial_E_first {y : ℝ} (hy : y ∈ Set.Ico (1 : ℝ) 60) :
    1 ≤ E (realWeights factorialWeights) y := by
  have hlo : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy.1)
  have hhi : ⌊y⌋₊ < 60 := (Nat.floor_lt (by linarith [hy.1] : 0 ≤ y)).mpr hy.2
  have hb := factorial_period_bound (by omega : ⌊y⌋₊ < 360360)
  rw [if_pos (by omega : 0 < ⌊y⌋₊ ∧ ⌊y⌋₊ < 60)] at hb
  have hr : (1000000 : ℝ) ≤ floorNumerator factorialWeights ⌊y⌋₊ := by exact_mod_cast hb
  rw [E_realWeights]
  linarith

/-- An unconditional recurrence with enough margin to preserve the RS12 slope. -/
theorem psi_factorial_recurrence {x : ℝ} (hx : 500000 ≤ x) :
    ψ x ≤ 1.021 * x + ψ (x / 60) := by
  have h := psi_diff_le_weighted (w := realWeights factorialWeights) (a := 60)
    (by norm_num) (by linarith : 0 < x) (fun y _ => factorial_E_nonneg y)
    (fun _ hy => factorial_E_first hy)
  have hb := factorial_upper hx
  linarith

end RS12Factorial
