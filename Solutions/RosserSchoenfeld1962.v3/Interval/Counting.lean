/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

namespace RSInterval
open Finset Real

/-- The prime interval uses an open left and closed right endpoint. -/
noncomputable def primes (x y : ℝ) : Finset ℕ := Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊x⌋₊

lemma mem_primes {x y : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primes x y ↔ p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  simp only [primes, mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hy, hp⟩, hn⟩
    have hy0 : 0 ≤ y := (Nat.floor_pos.mp (hp.pos.trans_le hy)).trans' (by norm_num)
    refine ⟨hp, ?_, (Nat.le_floor_iff hy0).mp hy⟩
    by_contra h
    exact hn ⟨Nat.le_floor (le_of_not_gt h), hp⟩
  · rintro ⟨hp, hxp, hpy⟩
    exact ⟨⟨Nat.le_floor hpy, hp⟩, fun h =>
      (not_le_of_gt hxp) ((Nat.le_floor_iff hx).mp h.1)⟩

lemma card_primes {x y : ℝ} (hxy : x ≤ y) :
    ((primes x y).card : ℝ) = IEANTN.primeCounting y - IEANTN.primeCounting x := by
  rw [primes, card_sdiff_of_subset (Nat.primesLE_mono (Nat.floor_mono hxy)),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting,
    Nat.cast_sub (Nat.monotone_primeCounting (Nat.floor_mono hxy))]
  rfl

lemma theta_sub_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Chebyshev.theta y - Chebyshev.theta x ≤
      (IEANTN.primeCounting y - IEANTN.primeCounting x) * log y := by
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
    ← sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_mono hxy)), ← card_primes hxy]
  calc
    _ ≤ ∑ _p ∈ primes x y, log y := by
      apply sum_le_sum
      intro p hp
      have hm := (mem_primes hx).mp hp
      exact log_le_log (by exact_mod_cast hm.1.pos) hm.2.2
    _ = _ := by simp

lemma list_le_count {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ps : List ℕ)
    (hs : ps.IsChain (· < ·))
    (hp : ∀ p ∈ ps, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y) :
    (ps.length : ℝ) ≤ IEANTN.primeCounting y - IEANTN.primeCounting x := by
  have hn : ps.Nodup := (List.isChain_iff_pairwise.mp hs).nodup
  rw [← card_primes hxy, ← List.toFinset_card_of_nodup hn]
  exact_mod_cast card_le_card (show ps.toFinset ⊆ primes x y from fun p h =>
    (mem_primes hx).mpr (hp p (List.mem_toFinset.mp h)))

end RSInterval
