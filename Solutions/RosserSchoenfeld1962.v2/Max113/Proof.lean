/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Max113.Finite
import RS12.Proof

namespace RS12Max113
open Chebyshev

/-- Positivity of the symbolic optimum, including for the interval below the first jump. -/
theorem psi_113_pos : 0 < ψ (113 : ℝ) := by
  have := psi_113_lower
  linarith

private theorem below_separator {x : ℝ} (hx : 0 < x) (h : ψ x < 1.03882 * x) :
    113 * ψ x < x * ψ (113 : ℝ) := by
  have := mul_lt_mul_of_pos_left psi_113_lower hx
  nlinarith

/-- The improved accumulator bounds every finite integer other than the equality endpoint. -/
theorem finite_integer_strict {n : ℕ} (hn : 0 < n) (hcut : n ≤ 500000) (hne : n ≠ 113) :
    113 * ψ (n : ℝ) < (n : ℝ) * ψ (113 : ℝ) := by
  apply below_separator (by exact_mod_cast hn)
  by_cases hs : n ≤ 600
  · exact small_integer hn hs hne
  · have hb := finite_integer (by omega : 600 < n) hcut
    have hr : (n : ℝ) ≤ 500000 := by exact_mod_cast hcut
    nlinarith

/-- The recurrence plus (3.35) already gives a strict tail below the symbolic optimum.
No induction with an approximated optimum, and no new tail certificate, is needed. -/
theorem tail_strict {x : ℝ} (hx : 500000 ≤ x) :
    113 * ψ x < x * ψ (113 : ℝ) := by
  apply below_separator (by linarith)
  have hr := RS12Factorial.psi_factorial_recurrence hx
  have hb := RS_prime.theorem_12 (x := x / 60) (by linarith)
  dsimp [RS_prime.c₀] at hb
  linarith

/-- The strict division-free maximum theorem, for every positive real except 113. -/
theorem psi_strict_maximum {x : ℝ} (hx : 0 < x) (hne : x ≠ 113) :
    113 * ψ x < x * ψ (113 : ℝ) := by
  by_cases hlarge : 500000 ≤ x
  · exact tail_strict hlarge
  have hf : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx.le
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  by_cases hz : ⌊x⌋₊ = 0
  · rw [hz]
    norm_num only [Nat.cast_zero, psi_zero, mul_zero]
    exact mul_pos hx psi_113_pos
  by_cases he : ⌊x⌋₊ = 113
  · rw [he]
    have hx113 : (113 : ℝ) < x := by
      norm_num [he] at hf
      exact lt_of_le_of_ne hf (Ne.symm hne)
    exact mul_lt_mul_of_pos_right hx113 psi_113_pos
  have hc : ⌊x⌋₊ ≤ 500000 := by
    exact_mod_cast (hf.trans (le_of_lt (lt_of_not_ge hlarge)))
  exact (finite_integer_strict (by omega) hc he).trans_le
    (mul_le_mul_of_nonneg_right hf psi_113_pos.le)

/-- Equality at 113 supplies the non-strict division-free version. -/
theorem psi_maximum {x : ℝ} (hx : 0 < x) :
    113 * ψ x ≤ x * ψ (113 : ℝ) := by
  by_cases he : x = 113
  · subst x; rfl
  · exact (psi_strict_maximum hx he).le

theorem ratio_maximum (x : ℝ) (hx : 0 < x) :
    ψ x / x ≤ ψ (113 : ℝ) / 113 := by
  apply (div_le_div_iff₀ hx (by norm_num : (0 : ℝ) < 113)).mpr
  simpa only [mul_comm] using psi_maximum hx

theorem ratio_unique_maximum (x : ℝ) (hx : 0 < x) :
    (ψ x / x = ψ (113 : ℝ) / 113 ↔ x = 113) := by
  constructor
  · intro he
    by_contra hne
    have hs : ψ x / x < ψ (113 : ℝ) / 113 := by
      apply (div_lt_div_iff₀ hx (by norm_num : (0 : ℝ) < 113)).mpr
      simpa only [mul_comm] using psi_strict_maximum hx hne
    exact (ne_of_lt hs) he
  · rintro rfl; rfl

end RS12Max113
