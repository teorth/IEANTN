/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PNT+ contributors
-/
import IEANTN.Nodes.RosserSchoenfeld1962.v3.Conclusions
import Mathlib.Tactic

/-! Secondary endpoint check adapted from PNT+ workspace material
`Erdos306/RSPrimeSums.lean`; see provenance.json for its source snapshot hash.
That material is not part of the pinned public PNT+ commit. This self-contained
proof takes the v3 conclusion as an explicit hypothesis and imports no source axiom. -/
namespace RSInterval.Dyadic
open Finset

def dyadicBlock (k : ℕ) : Finset ℕ := (Finset.Ico (2^k) (2^(k+1))).filter Nat.Prime

/-- `2 ^ n` is not prime once `n ≥ 2` (it has the proper divisor `2`). -/
lemma two_pow_not_prime {n : ℕ} (hn : 2 ≤ n) : ¬ (2 ^ n).Prime := by
  intro hp
  have hdvd : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have heq : (2 : ℕ) = 2 ^ n := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd
  have hge : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- `π n = π' n` when `n` is not prime (no contribution from `n` itself). -/
lemma primeCounting_eq_primeCounting'_of_not_prime {n : ℕ} (hn : ¬ n.Prime) :
    Nat.primeCounting n = Nat.primeCounting' n := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ, ite_eq_right hn, Nat.add_zero]

/-- The dyadic block `[2ᵏ, 2ᵏ⁺¹)` has exactly `π'(2ᵏ⁺¹) − π'(2ᵏ)` primes. -/
lemma dyadicBlock_card_eq (k : ℕ) :
    (dyadicBlock k).card
      = Nat.primeCounting' (2 ^ (k + 1)) - Nat.primeCounting' (2 ^ k) := by
  have hle : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
  have hsub : Nat.primesBelow (2 ^ k) ⊆ Nat.primesBelow (2 ^ (k + 1)) := by
    intro p hp
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hle, hp.2⟩
  have hset : dyadicBlock k = Nat.primesBelow (2 ^ (k + 1)) \ Nat.primesBelow (2 ^ k) := by
    ext p
    simp only [dyadicBlock, Nat.primesBelow, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨h2, hp⟩, fun h => absurd h.1 (not_lt.mpr h1)⟩
    · rintro ⟨⟨h2, hp⟩, hn⟩
      refine ⟨⟨?_, h2⟩, hp⟩
      by_contra h
      exact hn ⟨not_le.mp h, hp⟩
  have hkey : (dyadicBlock k).card + Nat.primeCounting' (2 ^ k)
      = Nat.primeCounting' (2 ^ (k + 1)) := by
    rw [hset, ← Nat.primesBelow_card_eq_primeCounting' (2 ^ k),
      ← Nat.primesBelow_card_eq_primeCounting' (2 ^ (k + 1))]
    exact Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- **Dyadic prime density**, derived from Rosser–Schoenfeld
Corollary 3, eq. (3.8).  For `k ≥ 5`,
`2ᵏ / (2 log 2ᵏ) ≤ #{p prime : 2ᵏ ≤ p < 2ᵏ⁺¹}`. -/
theorem dyadic_prime_density (h38 : RosserSchoenfeld1962.v3.equation_3_8) (k : ℕ) (hk : 5 ≤ k) :
    (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ ((dyadicBlock k).card : ℝ) := by
  -- Abbreviations and basic positivity.
  set x : ℝ := (2 : ℝ) ^ k with hxdef
  have hx32 : (32 : ℝ) ≤ x := by
    rw [hxdef]
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hx1 : (1 : ℝ) < x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  -- Floor evaluations: ⌊x⌋ = 2ᵏ and ⌊2x⌋ = 2ᵏ⁺¹.
  have hxnat : x = ((2 ^ k : ℕ) : ℝ) := by rw [hxdef]; push_cast; ring
  have h2xnat : 2 * x = ((2 ^ (k + 1) : ℕ) : ℝ) := by rw [hxdef]; push_cast; ring
  have hfloorx : ⌊x⌋₊ = 2 ^ k := by rw [hxnat, Nat.floor_natCast]
  have hfloor2x : ⌊2 * x⌋₊ = 2 ^ (k + 1) := by rw [h2xnat, Nat.floor_natCast]
  -- π at the two endpoints equals π' (the powers of 2 are not prime).
  have hk2 : 2 ≤ k := by omega
  have hπx : Nat.primeCounting ⌊x⌋₊ = Nat.primeCounting' (2 ^ k) := by
    rw [hfloorx, primeCounting_eq_primeCounting'_of_not_prime (two_pow_not_prime hk2)]
  have hπ2x : Nat.primeCounting ⌊2 * x⌋₊ = Nat.primeCounting' (2 ^ (k + 1)) := by
    rw [hfloor2x, primeCounting_eq_primeCounting'_of_not_prime (two_pow_not_prime (by omega))]
  -- The RS difference equals the block cardinality (as reals).
  have hmono : Nat.primeCounting' (2 ^ k) ≤ Nat.primeCounting' (2 ^ (k + 1)) :=
    Nat.monotone_primeCounting' (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
  have hcardR :
      (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ)
        = ((dyadicBlock k).card : ℝ) := by
    rw [hπx, hπ2x, dyadicBlock_card_eq, Nat.cast_sub hmono]
  -- Rosser–Schoenfeld Corollary 3 at this `x`.
  have hRS := h38 x (by linarith)
  change 3 * x / (5 * Real.log x) <
    (Nat.primeCounting ⌊2*x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) at hRS
  rw [hcardR] at hRS
  -- Close: 2ᵏ/(2 log 2ᵏ) = x/(2 log x) ≤ 3x/(5 log x) < card.
  have hlog_eq : Real.log (2 ^ k) = Real.log x := by rw [hxdef]
  rw [hlog_eq]
  have hstep : x / (2 * Real.log x) ≤ 3 * x / (5 * Real.log x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hxpos, hlogpos]
  calc x / (2 * Real.log x) ≤ 3 * x / (5 * Real.log x) := hstep
    _ ≤ _ := le_of_lt hRS

end RSInterval.Dyadic
