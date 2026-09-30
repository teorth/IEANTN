/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.KernelLogs
import Mathlib.NumberTheory.Chebyshev

set_option maxRecDepth 100000

namespace RS12PsiInteger
open Real Finset ArithmeticFunction Chebyshev

/-- Integer units for an upper logarithm bound, with scale eight. -/
def logUnits (p : ℕ) : ℕ := Nat.log2 (p ^ 8) + 1

/-- An integer majorant for each von Mangoldt value. -/
private def psiUnitTerm (n : ℕ) : ℕ :=
  if IsPrimePow n then logUnits n.minFac else 0

/-- A block checks all required slopes and its final accumulator. -/
def checkPsiBlock (start : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, acc, target => acc == target
  | count + 1, acc, target =>
    let next := start + 1
    let acc' := acc + psiUnitTerm next
    (!(Nat.ble 600 next) || Nat.ble (693148 * acc') (8310632 * next)) &&
      checkPsiBlock next count acc' target

/-- Taking eight powers turns a binary length into an explicit logarithm bound. -/
theorem log_le_units {p : ℕ} (hp : 0 < p) :
    log (p : ℝ) ≤ (logUnits p : ℝ) * 693148 / 8000000 := by
  have hn : p ^ 8 < 2 ^ logUnits p := by
    simpa only [logUnits, Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self
      (by norm_num : 1 < (2 : ℕ)) (p ^ 8)
  have hr : (p : ℝ)^8 ≤ (2 : ℝ)^(logUnits p) := by exact_mod_cast hn.le
  have hl := Real.log_le_log (show (0 : ℝ) < (p : ℝ)^8 by positivity) hr
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  have hc := mul_le_mul_of_nonneg_left RS12Factorial.kernel_log_two
    (Nat.cast_nonneg (logUnits p) : (0 : ℝ) ≤ logUnits p)
  nlinarith

/-- Every integer unit term bounds the actual von Mangoldt function. -/
private theorem vonMangoldt_le_units (n : ℕ) :
    vonMangoldt n ≤ (psiUnitTerm n : ℝ) * 693148 / 8000000 := by
  rw [vonMangoldt_apply, psiUnitTerm]
  split_ifs with hp
  · exact log_le_units (Nat.minFac_pos n)
  · norm_num

/-- Incrementing a natural endpoint adds exactly one von Mangoldt value. -/
theorem psi_succ (n : ℕ) :
    ψ (n + 1 : ℕ) = ψ (n : ℕ) + vonMangoldt (n + 1) := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]

/-- Soundness for a block, including the accumulator passed to the next block. -/
theorem checkPsiBlock_sound {start count acc target : ℕ}
    (hc : checkPsiBlock start count acc target = true)
    (hacc : ψ (start : ℕ) ≤ (acc : ℝ) * 693148 / 8000000) :
    ψ (start + count : ℕ) ≤ (target : ℝ) * 693148 / 8000000 ∧
      ∀ m : ℕ, start < m → m ≤ start + count → 600 ≤ m →
        ψ (m : ℕ) ≤ 1.038829 * m := by
  induction count generalizing start acc with
  | zero =>
    have he : acc = target := by simpa [checkPsiBlock] using hc
    constructor
    · simpa [he] using hacc
    · intro m hlo hhi _; omega
  | succ count ih =>
    simp only [checkPsiBlock, Bool.and_eq_true] at hc
    have hnext : ψ (start + 1 : ℕ) ≤
        ((acc + psiUnitTerm (start + 1) : ℕ) : ℝ) * 693148 / 8000000 := by
      rw [psi_succ]
      have ht := vonMangoldt_le_units (start + 1)
      push_cast
      linarith
    have htail := ih hc.2 hnext
    refine ⟨by simpa only [Nat.add_assoc, Nat.add_comm 1] using htail.1, ?_⟩
    intro m hlo hhi hm
    by_cases he : m = start + 1
    · subst m
      have hb : 693148 * (acc + psiUnitTerm (start + 1)) ≤ 8310632 * (start + 1) := by
        have hble : Nat.ble 600 (start + 1) = true := by simpa only [Nat.ble_eq] using hm
        have hh := hc.1
        rw [hble] at hh
        simpa only [Bool.not_true, Bool.false_or, Nat.ble_eq] using hh
      have hr : (693148 : ℝ) * ((acc : ℝ) + psiUnitTerm (start + 1)) ≤
          8310632 * ((start : ℝ) + 1) := by exact_mod_cast hb
      push_cast at hnext ⊢
      nlinarith
    · exact htail.2 m (by omega) (by omega) hm

end RS12PsiInteger
