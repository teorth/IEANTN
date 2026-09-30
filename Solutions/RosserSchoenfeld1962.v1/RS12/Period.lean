/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.Weights
import RS12.Factorial

open Real Finsupp Finset Chebyshev
namespace RS12Factorial

/-- Interpret the integer certificate as finitely supported real weights. -/
noncomputable def realWeights (cs : List (ℕ × ℤ)) : ℕ →₀ ℝ :=
  (cs.map (fun dw => Finsupp.single dw.1 ((dw.2 : ℝ) / 1000000))).sum

theorem realWeights_sum (cs : List (ℕ × ℤ)) (f : ℕ → ℝ) :
    (realWeights cs).sum (fun m b => b * f m) =
      (cs.map (fun dw => ((dw.2 : ℝ) / 1000000) * f dw.1)).sum := by
  induction cs with
  | nil => simp [realWeights]
  | cons dw cs ih =>
    simp only [realWeights, List.map_cons, List.sum_cons] at *
    rw [Finsupp.sum_add_index (by simp) (by intros; ring), Finsupp.sum_single_index (by simp), ih]

theorem E_realWeights (cs : List (ℕ × ℤ)) (y : ℝ) :
    Chebyshev.E (realWeights cs) y = (floorNumerator cs ⌊y⌋₊ : ℝ) / 1000000 := by
  rw [Chebyshev.E, realWeights_sum]
  induction cs with
  | nil => simp [floorNumerator]
  | cons dw cs ih =>
    simp only [List.map_cons, List.sum_cons, floorNumerator, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] at *
    rw [← Nat.floor_div_natCast, ih]
    ring

/-- A divisible period translates every individual floor by an integer. -/
private theorem floorNumerator_add_period (cs : List (ℕ × ℤ)) {P : ℕ}
    (hd : ∀ dw ∈ cs, dw.1 ∣ P) (n : ℕ) :
    floorNumerator cs (n + P) = floorNumerator cs n + floorNumerator cs P := by
  induction cs with
  | nil => simp [floorNumerator]
  | cons dw cs ih =>
    have hdiv := hd dw (by simp)
    have hrest : ∀ dw ∈ cs, dw.1 ∣ P := fun dw h => hd dw (by simp [h])
    simp only [floorNumerator, List.map_cons, List.sum_cons] at *
    rw [Nat.add_div_of_dvd_left hdiv, Nat.cast_add, mul_add, ih hrest]
    ring

set_option linter.unusedVariables false in
-- Retain the existing positive-period hypothesis and binder name in the public interface.
/-- Balance makes the floor kernel depend only on one finite period. -/
theorem floorNumerator_mod_period (cs : List (ℕ × ℤ)) {P : ℕ} (hP : 0 < P)
    (hd : ∀ dw ∈ cs, dw.1 ∣ P) (hb : floorNumerator cs P = 0) (n : ℕ) :
    floorNumerator cs n = floorNumerator cs (n % P) := by
  have hp (m q : ℕ) : floorNumerator cs (m + q * P) = floorNumerator cs m := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, ← add_assoc, floorNumerator_add_period cs hd, hb, add_zero, ih]
  have hn : n % P + (n / P) * P = n := by simpa only [Nat.mul_comm] using Nat.mod_add_div n P
  calc
    floorNumerator cs n = floorNumerator cs (n % P + (n / P) * P) := congrArg _ hn.symm
    _ = floorNumerator cs (n % P) := hp _ _

-- Legacy list-based checker, kept local with its soundness proofs.
private def checkFloorBlock (cs : List (ℕ × ℤ)) (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    decide ((if 0 < start ∧ start < 60 then (1000000 : ℤ) else 0) ≤ floorNumerator cs start) &&
      checkFloorBlock cs (start + 1) count

private def checkFactorialPeriod : Bool :=
  (List.range 3003).all (fun k => checkFloorBlock factorialWeights (120 * k) 120)

/-- Soundness of each bounded integer check. -/
private theorem checkFloorBlock_sound {cs : List (ℕ × ℤ)} {start count : ℕ}
    (hc : checkFloorBlock cs start count = true) {n : ℕ}
    (hlo : start ≤ n) (hhi : n < start + count) :
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤ floorNumerator cs n := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    simp only [checkFloorBlock, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hn : n = start
    · simpa [hn] using hc.1
    · exact ih hc.2 (by omega) (by omega)

/-- Turn the chunked Boolean computation into the exact finite certificate. -/
private theorem factorial_checked_sound (hc : checkFactorialPeriod = true) {n : ℕ} (hn : n < 360360) :
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤ floorNumerator factorialWeights n := by
  have hk : n / 120 ∈ List.range 3003 := by simp only [List.mem_range]; omega
  have hb := (List.all_eq_true.mp hc) (n / 120) hk
  exact checkFloorBlock_sound hb (by omega) (by omega)

/-- Join adjacent certified integer intervals without repeating their computation. -/
theorem floorBlock_join {cs : List (ℕ × ℤ)} {lo mid hi : ℕ}
    (hl : ∀ n, lo ≤ n → n < mid →
      (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤ floorNumerator cs n)
    (hr : ∀ n, mid ≤ n → n < hi →
      (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤ floorNumerator cs n) :
    ∀ n, lo ≤ n → n < hi →
      (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤ floorNumerator cs n := by
  intro n hn hhi
  by_cases hm : n < mid
  · exact hl n hn hm
  · exact hr n (by omega) hhi

end RS12Factorial
