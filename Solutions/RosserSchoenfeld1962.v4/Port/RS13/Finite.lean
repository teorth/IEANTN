/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Port.RS13.Numeric
import Port.RS13.Logs

set_option maxRecDepth 100000

namespace RS5Historical.Theorem13
open Real Chebyshev Finset

private theorem minFac_mem {n : ℕ} (hn : n ∈ candidates) : n.minFac ∈ primeBases := by
  rw [candidates, Finset.mem_filter, Finset.mem_image] at hn
  obtain ⟨⟨⟨p,k⟩, hpk, rfl⟩, _⟩ := hn
  obtain ⟨hp, hk⟩ := Finset.mem_product.mp hpk
  have hprime := (Finset.mem_filter.mp hp).2
  rw [hprime.pow_minFac (by have := (Finset.mem_Icc.mp hk).1; omega)]
  rw [primeBases]
  exact hp

/-- Integer logarithm bounds accumulate over exactly the proper prime powers. -/
theorem gap_bounds {m : ℕ} (hm : m ≤ 46656) :
    (lowerSum m : ℝ) / 1000000 ≤ ψ (m : ℝ) - θ (m : ℝ) ∧
      ψ (m : ℝ) - θ (m : ℝ) ≤ (upperSum m : ℝ) / 1000000 := by
  classical
  rw [gap_eq_sum_candidates (by exact_mod_cast hm)]
  constructor
  · rw [lowerSum, ← candidates_eq, Nat.cast_sum, sum_div]
    apply sum_le_sum
    intro n hn
    have h := (log_bounds (minFac_mem hn)).1
    by_cases hnm : n ≤ m
    · simpa only [Nat.cast_le, hnm, if_true] using h
    · simp only [Nat.cast_le, hnm, if_false, Nat.cast_zero, zero_div, le_refl]
  · rw [upperSum, ← candidates_eq, Nat.cast_sum, sum_div]
    apply sum_le_sum
    intro n hn
    have h := (log_bounds (minFac_mem hn)).2
    by_cases hnm : n ≤ m
    · simpa only [Nat.cast_le, hnm, if_true] using h
    · simp only [Nat.cast_le, hnm, if_false, Nat.cast_zero, zero_div, le_refl]

attribute [local irreducible] upperSum lowerSum jumpList

/-- Every jump other than 361 has the stronger bound with coefficient 7/5. -/
theorem finite_nonanchor {m : ℕ} (hm : m ∈ candidates) (hne : m ≠ 361) :
    ψ (m : ℝ) - θ (m : ℝ) ≤ (7 / 5) * sqrt m := by
  have hb := (gap_bounds (mem_candidates_iff.mp hm).2.2).2
  have hi : 25 * (upperSum m : ℝ)^2 ≤ 49 * 1000000000000 * (m : ℝ) := by
    exact_mod_cast checked_squares hm hne
  have hs := sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  have hu : (upperSum m : ℝ) / 1000000 ≤ (7 / 5) * sqrt m := by
    have hleft : (0 : ℝ) ≤ (upperSum m : ℝ) / 1000000 := by positivity
    have hright : (0 : ℝ) ≤ (7 / 5) * sqrt m := by positivity
    apply (sq_le_sq₀ hleft hright).mp
    nlinarith
  exact hb.trans hu

/-- The strict historical decimal is separated from the maximum by exact integers. -/
theorem anchor_bounds :
    (7 / 5 : ℝ) * 19 ≤ ψ 361 - θ 361 ∧ ψ 361 - θ 361 < 1.42620 * 19 := by
  have hb := gap_bounds (m := 361) (by norm_num)
  have hl : (26600000 : ℝ) ≤ lowerSum 361 := by exact_mod_cast checked_anchor.1
  have hu : (upperSum 361 : ℝ) < 27097800 := by exact_mod_cast checked_anchor.2
  constructor <;> linarith

end RS5Historical.Theorem13
