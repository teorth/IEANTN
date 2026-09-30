/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.PsiInteger
import Mathlib.Data.Nat.Factorization.PrimePow

set_option maxRecDepth 100000

namespace RS12PsiInteger
open Real Finset ArithmeticFunction Chebyshev

/-- A zero exponent encodes a proper coprime factor; a positive exponent encodes a power. -/
private def checkFactor (n a k : ℕ) : Bool :=
  if k = 0 then decide (1 < a ∧ a < n ∧ n % a = 0 ∧ Nat.gcd a (n / a) = 1)
  else decide (0 < a ∧ a ^ k = n)

private def factorUnits (a k : ℕ) : ℕ := if k = 0 then 0 else logUnits a

/-- Proper coprime factors rule out prime powers without primality testing. -/
theorem vonMangoldt_eq_zero_of_coprime_factors {n a : ℕ}
    (ha : 1 < a) (han : a < n) (hd : n % a = 0) (hg : Nat.gcd a (n / a) = 1) :
    vonMangoldt n = 0 := by
  apply vonMangoldt_eq_zero_iff.mpr
  intro hp
  have had : a ∣ n := Nat.dvd_of_mod_eq_zero hd
  have he : a * (n / a) = n := Nat.mul_div_cancel' had
  have hc : Nat.Coprime a (n / a) := hg
  have hq : 0 < n / a := Nat.div_pos han.le (by omega)
  have hdiv : n ∣ a * (n / a) := by rw [he]
  rcases (hc.isPrimePow_dvd_mul hp).mp hdiv with h | h
  · have := Nat.le_of_dvd (by omega : 0 < a) h
    omega
  · have := Nat.le_of_dvd hq h
    nlinarith

/-- The factor witness bounds one von Mangoldt term. -/
private theorem vonMangoldt_le_factorUnits {n a k : ℕ} (hc : checkFactor n a k = true) :
    vonMangoldt n ≤ (factorUnits a k : ℝ) * 693148 / 8000000 := by
  by_cases hk : k = 0
  · simp only [checkFactor, hk, if_pos, decide_eq_true_eq] at hc
    rw [vonMangoldt_eq_zero_of_coprime_factors hc.1 hc.2.1 hc.2.2.1 hc.2.2.2]
    simp [factorUnits, hk]
  · simp only [checkFactor, hk, if_false, decide_eq_true_eq] at hc
    rw [← hc.2, vonMangoldt_apply_pow hk]
    simpa only [factorUnits, if_neg hk] using vonMangoldt_le_log.trans (log_le_units hc.1)

/-- Packed arithmetic witnesses use five low bits for the exponent. -/
private def hintUnits (code : ℕ) : ℕ := factorUnits (code / 32) (code % 32)

def checkWitnessBlock (start : ℕ) : List ℕ → ℕ → ℕ → Bool
  | [], acc, target => acc == target
  | code :: cs, acc, target =>
    let next := start + 1
    let acc' := acc + hintUnits code
    checkFactor next (code / 32) (code % 32) &&
      ((!(Nat.ble 600 next) || Nat.ble (693148 * acc') (8310632 * next)) &&
        checkWitnessBlock next cs acc' target)

/-- Soundness of a block of supplied factorization witnesses. -/
theorem checkWitnessBlock_sound {start acc target : ℕ} {cs : List ℕ}
    (hc : checkWitnessBlock start cs acc target = true)
    (hacc : ψ (start : ℕ) ≤ (acc : ℝ) * 693148 / 8000000) :
    ψ (start + cs.length : ℕ) ≤ (target : ℝ) * 693148 / 8000000 ∧
      ∀ m : ℕ, start < m → m ≤ start + cs.length → 600 ≤ m →
        ψ (m : ℕ) ≤ 1.038829 * m := by
  induction cs generalizing start acc with
  | nil =>
    have he : acc = target := by simpa [checkWitnessBlock] using hc
    constructor
    · simpa [he] using hacc
    · intro m hlo hhi _; simp only [List.length_nil, Nat.add_zero] at hhi; omega
  | cons code cs ih =>
    simp only [checkWitnessBlock, Bool.and_eq_true] at hc
    have hnext : ψ (start + 1 : ℕ) ≤
        ((acc + hintUnits code : ℕ) : ℝ) * 693148 / 8000000 := by
      rw [psi_succ]
      have ht := vonMangoldt_le_factorUnits hc.1
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
theorem psiRange_join {lo mid hi : ℕ}
    (hl : ∀ m : ℕ, lo < m → m ≤ mid → ψ (m : ℕ) ≤ 1.038829 * m)
    (hr : ∀ m : ℕ, mid < m → m ≤ hi → ψ (m : ℕ) ≤ 1.038829 * m) :
    ∀ m : ℕ, lo < m → m ≤ hi → ψ (m : ℕ) ≤ 1.038829 * m := by
  intro m hlo hhi
  by_cases hm : m ≤ mid
  · exact hl m hlo hm
  · exact hr m (by omega) hhi

end RS12PsiInteger
