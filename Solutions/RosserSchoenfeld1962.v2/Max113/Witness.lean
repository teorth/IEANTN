/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Max113.Logs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.PrimePow

namespace RS12PsiInteger
open Real Finset ArithmeticFunction Chebyshev

def logUnits (p : ℕ) : ℕ := Nat.log2 (p ^ 8) + 1

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

/-- Incrementing a natural endpoint adds exactly one von Mangoldt value. -/
theorem psi_succ (n : ℕ) :
    ψ (n + 1 : ℕ) = ψ (n : ℕ) + vonMangoldt (n + 1) := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]

/-- A zero exponent encodes a proper coprime factor; a positive exponent encodes a power. -/
def checkFactor (n a k : ℕ) : Bool :=
  if k = 0 then decide (1 < a ∧ a < n ∧ n % a = 0 ∧ Nat.gcd a (n / a) = 1)
  else decide (0 < a ∧ a ^ k = n)

def factorUnits (a k : ℕ) : ℕ := if k = 0 then 0 else logUnits a

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
theorem vonMangoldt_le_factorUnits {n a k : ℕ} (hc : checkFactor n a k = true) :
    vonMangoldt n ≤ (factorUnits a k : ℝ) * 693148 / 8000000 := by
  by_cases hk : k = 0
  · simp only [checkFactor, hk, if_pos, decide_eq_true_eq] at hc
    rw [vonMangoldt_eq_zero_of_coprime_factors hc.1 hc.2.1 hc.2.2.1 hc.2.2.2]
    simp [factorUnits, hk]
  · simp only [checkFactor, hk, if_false, decide_eq_true_eq] at hc
    rw [← hc.2, vonMangoldt_apply_pow hk]
    simpa only [factorUnits, if_neg hk] using vonMangoldt_le_log.trans (log_le_units hc.1)

/-- Packed arithmetic witnesses use five low bits for the exponent. -/
def hintUnits (code : ℕ) : ℕ := factorUnits (code / 32) (code % 32)

def checkWitnessBlock (start : ℕ) : List ℕ → ℕ → ℕ → Bool
  | [], acc, target => acc == target
  | code :: cs, acc, target =>
    let next := start + 1
    let acc' := acc + hintUnits code
    checkFactor next (code / 32) (code % 32) &&
      ((!(Nat.ble 600 next) || Nat.ble (693148 * acc') (8310632 * next)) &&
        checkWitnessBlock next cs acc' target)


end RS12PsiInteger
