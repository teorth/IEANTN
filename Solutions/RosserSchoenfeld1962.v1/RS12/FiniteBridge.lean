/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.Small

open Real Chebyshev
namespace RS12Factorial

/-- Convert a certified finite integer interval to the strict real RS12 bound. -/
theorem psi_finite_of_integer_bounds {B : ℕ}
    (hcert : ∀ m : ℕ, 600 < m → m ≤ B → ψ (m : ℕ) ≤ 1.038829 * m)
    {x : ℝ} (hx : 0 < x) (hB : x ≤ B) : ψ x < RS_prime.c₀ * x := by
  by_cases hs : x ≤ 600
  · exact RS12Small.small hx hs
  have hl : 600 < x := lt_of_not_ge hs
  have hnpos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx.le
  rw [Chebyshev.psi_eq_psi_coe_floor]
  by_cases hn : ⌊x⌋₊ ≤ 600
  · have h := RS12Small.small (x := (⌊x⌋₊ : ℝ))
      (by exact_mod_cast hnpos) (by exact_mod_cast hn)
    exact h.trans_le (mul_le_mul_of_nonneg_left hfloor (by norm_num [RS_prime.c₀]))
  · have hnb : ⌊x⌋₊ ≤ B := by
      have hh := Nat.floor_mono hB
      simpa only [Nat.floor_natCast] using hh
    have h := hcert ⌊x⌋₊ (by omega) hnb
    calc
      ψ (⌊x⌋₊ : ℝ) ≤ 1.038829 * ⌊x⌋₊ := h
      _ ≤ 1.038829 * x := mul_le_mul_of_nonneg_left hfloor (by norm_num)
      _ < RS_prime.c₀ * x := by dsimp [RS_prime.c₀]; nlinarith

/-- The recurrence argument is strictly smaller for natural-floor induction. -/
theorem floor_div_sixty_lt {x : ℝ} (hx : 2 ≤ x) : ⌊x / 60⌋₊ < ⌊x⌋₊ := by
  have hf := Nat.lt_floor_add_one x
  have hp : 0 ≤ x / 60 := by positivity
  apply (Nat.floor_lt hp).mpr
  linarith

end RS12Factorial
