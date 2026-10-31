/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import RS12.PsiWitness
import Max113.Private

namespace RS12Max113
open Real Chebyshev RS12PsiInteger ArithmeticFunction

set_option maxRecDepth 100000

private abbrev hintUnits : ℕ → ℕ :=
  rs12_private% RS12.PsiWitness RS12PsiInteger.hintUnits

/-- Soundness of a block of supplied factorization witnesses. -/
theorem shifted_sound {start acc target : ℕ} {δ : ℝ} {cs : List ℕ}
    (hc : checkWitnessBlock start cs acc target = true)
    (hacc : (ψ (start : ℕ) + δ) ≤ (acc : ℝ) * 693148 / 8000000) :
    (ψ (start + cs.length : ℕ) + δ) ≤ (target : ℝ) * 693148 / 8000000 ∧
      ∀ m : ℕ, start < m → m ≤ start + cs.length → 600 ≤ m →
        (ψ (m : ℕ) + δ) ≤ 1.038829 * m := by
  induction cs generalizing start acc with
  | nil =>
    have he : acc = target := by simpa [checkWitnessBlock] using hc
    constructor
    · simpa [he] using hacc
    · intro m hlo hhi _; simp only [List.length_nil, Nat.add_zero] at hhi; omega
  | cons code cs ih =>
    simp only [checkWitnessBlock, Bool.and_eq_true] at hc
    have hnext : (ψ (start + 1 : ℕ) + δ) ≤
        ((acc + hintUnits code : ℕ) : ℝ) * 693148 / 8000000 := by
      rw [psi_succ]
      have ht := (rs12_private% RS12.PsiWitness RS12PsiInteger.vonMangoldt_le_factorUnits) hc.1
      change vonMangoldt (start + 1) ≤ (hintUnits code : ℝ) * 693148 / 8000000 at ht
      push_cast
      linarith
    have htail := ih hc.2.2 hnext
    refine ⟨by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using htail.1, ?_⟩
    intro m hlo hhi hm
    by_cases he : m = start + 1
    · subst m
      have hb : 693148 * (acc + hintUnits code) ≤ 8310632 * (start + 1) := by
        have hble : Nat.ble 600 (start + 1) = true := by simpa only [Nat.ble_eq] using hm
        have hh := hc.2.1
        rw [hble] at hh
        simpa only [Bool.not_true, Bool.false_or, Nat.ble_eq] using hh
      have hr : (693148 : ℝ) * ((acc : ℝ) + hintUnits code) ≤
          8310632 * ((start : ℝ) + 1) := by exact_mod_cast hb
      push_cast at hnext ⊢
      nlinarith
    · exact htail.2 m (by omega) (by simp only [List.length_cons] at hhi; omega) hm

/-- Join adjacent finite ranges without repeating their computations. -/
theorem shifted_join {lo mid hi : ℕ} {δ : ℝ}
    (hl : ∀ m : ℕ, lo < m → m ≤ mid → (ψ (m : ℕ) + δ) ≤ 1.038829 * m)
    (hr : ∀ m : ℕ, mid < m → m ≤ hi → (ψ (m : ℕ) + δ) ≤ 1.038829 * m) :
    ∀ m : ℕ, lo < m → m ≤ hi → (ψ (m : ℕ) + δ) ≤ 1.038829 * m := by
  intro m hlo hhi
  by_cases hm : m ≤ mid
  · exact hl m hlo hm
  · exact hr m (by omega) hhi

end RS12Max113
