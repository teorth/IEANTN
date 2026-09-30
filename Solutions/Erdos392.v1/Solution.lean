/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Erdos392Dev
import IEANTN.Nodes.Erdos392.v1.Conclusions

/-!
# Solution for `Erdos392.v1`

Three conclusions. The two upper bounds come from `Erdos392Dev`, the port of
`PrimeNumberTheoremAnd/IEANTN/Erdos392.lean`, with two pieces of translation:

* its `Solution_1` produces a `Factorization n` — a multiset with side conditions — and the node
  states an ordinary indexed product, so the multiset is turned into a list and read off;
* its `Solution_2` places the cardinality bound *inside* the quantifier over factors. Pulling it
  out needs the case `t = 0` treated separately, which is where the node's shape is doing work: it
  says what one means without relying on the index type being nonempty.

The lower bound is not a port. PNT+ does not prove it, and without it the node would state half of
a two-sided asymptotic. It is four steps: `n! = ∏ aᵢ ≤ (n²)ᵗ`, take logarithms, apply Mathlib's
effective Stirling bound, and divide by `2 log n`.
-/

open Filter Nat Real

theorem Erdos392.v1.challenge_factors_le_n : Erdos392.v1.factors_le_n := by
  intro ε hε
  filter_upwards [Erdos392Sol.Solution_1 ε hε] with n hn
  obtain ⟨f, hf_bal, hf_card⟩ := hn
  refine ⟨f.a.toList.length, fun i ↦ f.a.toList.get i, ?_, ?_, ?_⟩
  · rw [← List.prod_ofFn, List.ofFn_get]
    have hprod : f.prod id = n ! := f.zero_total_imbalance hf_bal
    simp only [Erdos392Sol.Factorization.prod, Multiset.map_id] at hprod
    rw [← hprod, ← Multiset.prod_toList]
  · exact fun i ↦ f.ha _ (Multiset.mem_toList.mp (List.get_mem ..))
  · rwa [Multiset.length_toList]

theorem Erdos392.v1.challenge_factors_le_n_sq : Erdos392.v1.factors_le_n_sq := by
  intro ε hε
  filter_upwards [Erdos392Sol.Solution_2 ε hε, eventually_gt_atTop 2] with n hn hn2
  obtain ⟨t, a, hprod, hrest⟩ := hn
  refine ⟨t, a, hprod, fun i ↦ (hrest i).1, ?_⟩
  -- The bound sits inside the quantifier upstream, so `t = 0` has to be read off separately.
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hlog1 : 1 < Real.log n := by
      have : Real.exp 1 < (n : ℝ) := by
        calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          _ ≤ (3 : ℝ) := by norm_num
          _ ≤ (n : ℝ) := by exact_mod_cast hn2
      exact (Real.lt_log_iff_exp_lt (by positivity)).mpr this
    have hnpos : (0 : ℝ) < n := by positivity
    have h1 : (n : ℝ) / (2 * Real.log n) ≤ n / 2 := by
      gcongr
      linarith
    have h2 : 0 ≤ ε * n / Real.log n := by positivity
    simp only [Nat.cast_zero]
    linarith
  · exact (hrest ⟨0, ht⟩).2

theorem Erdos392.v1.challenge_factors_le_n_sq_lower : Erdos392.v1.factors_le_n_sq_lower := by
  intro n hn t a hprod hle
  have hn0 : n ≠ 0 := by omega
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos hn1
  -- `n! = ∏ aᵢ ≤ (n²)ᵗ`
  have hfac : (n ! : ℝ) ≤ ((n : ℝ) ^ 2) ^ t := by
    have hnat : (∏ i, a i) ≤ (n ^ 2) ^ t := by
      calc (∏ i : Fin t, a i) ≤ ∏ _i : Fin t, n ^ 2 := Finset.prod_le_prod fun i _ ↦ hle i
        _ = (n ^ 2) ^ t := by simp
    calc (n ! : ℝ) = ((∏ i, a i : ℕ) : ℝ) := by rw [hprod]
      _ ≤ (((n ^ 2) ^ t : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((n : ℝ) ^ 2) ^ t := by push_cast; ring
  -- take logarithms
  have hlog : Real.log (n !) ≤ t * (2 * Real.log n) := by
    calc Real.log (n !) ≤ Real.log (((n : ℝ) ^ 2) ^ t) :=
          Real.log_le_log (by positivity) hfac
      _ = t * (2 * Real.log n) := by
          rw [Real.log_pow, Real.log_pow]; push_cast; ring
  -- Stirling, effectively: `n log n - n + (log n)/2 + log(2π)/2 ≤ log n!`
  have hstir := Stirling.le_log_factorial_stirling hn0
  have h2pi : 0 < Real.log (2 * π) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  -- and divide by `2 log n`, the two dropped Stirling terms being positive
  have hgoal : (n : ℝ) / 2 - n / (2 * Real.log n)
      = ((n : ℝ) * Real.log n - n) / (2 * Real.log n) := by
    field_simp
  rw [hgoal, div_le_iff₀ (by positivity)]
  linarith
