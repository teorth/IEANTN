/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting

/-!
# `π(1500)` and `primorial 1500`, by the kernel

`decide +kernel` with Mathlib's `Nat.Prime` instance tries every divisor below `n`. On `[0, 1500]`
that took about fifty seconds per check, and the two checks in one proof went past ten gigabytes.
Trial division up to `√n`, proved equivalent to `Nat.Prime` once, brings both down to a few seconds.
-/

namespace ButheNumerics.v2.Dev

/-- Trial division by `d, d + 1, …` for at most `k` steps, stopping once `d * d > n`. -/
def noDivisorFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, d => n < d * d || (n % d != 0 && noDivisorFrom n k (d + 1))

theorem noDivisorFrom_iff (n k d : ℕ) :
    noDivisorFrom n k d = true ↔ ∀ m, d ≤ m → m < d + k → m * m ≤ n → ¬m ∣ n := by
  induction k generalizing d with
  | zero => simp only [noDivisorFrom, true_iff]; intro m h1 h2; omega
  | succ k ih =>
    simp only [noDivisorFrom, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      bne_iff_ne, ne_eq, ih]
    constructor
    · rintro (h | ⟨hd, h⟩) m hm1 hm2 hm3
      · exact absurd (Nat.mul_le_mul hm1 hm1) (by omega)
      · rcases hm1.eq_or_lt with rfl | hm1
        · exact fun hdvd ↦ hd (Nat.mod_eq_zero_of_dvd hdvd)
        · exact h m hm1 (by omega) hm3
    · intro h
      by_cases hn : n < d * d
      · exact Or.inl hn
      · exact Or.inr ⟨fun h0 ↦ h d le_rfl (by omega) (by omega) (Nat.dvd_of_mod_eq_zero h0),
          fun m hm1 hm2 ↦ h m (by omega) (by omega)⟩

/-- A primality test the kernel can run quickly. -/
def isPrime (n : ℕ) : Bool := 2 ≤ n && noDivisorFrom n n 2

theorem isPrime_iff (n : ℕ) : isPrime n = true ↔ n.Prime := by
  rw [isPrime, Bool.and_eq_true, decide_eq_true_eq, noDivisorFrom_iff, Nat.prime_def_le_sqrt]
  refine and_congr_right fun _ ↦ forall_congr' fun m ↦ ?_
  constructor
  · exact fun h hm hsq ↦ h hm (by nlinarith [Nat.le_sqrt.mp hsq]) (Nat.le_sqrt.mp hsq)
  · exact fun h hm _ hsq ↦ h hm (Nat.le_sqrt.mpr hsq)

theorem filter_prime (N : ℕ) :
    (Finset.range N).filter Nat.Prime = (Finset.range N).filter (isPrime · = true) :=
  Finset.filter_congr fun n _ ↦ (isPrime_iff n).symm

theorem primeCounting_1500 : Nat.primeCounting 1500 = 239 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range, filter_prime]
  decide +kernel

theorem primorial_1500 : 2 ^ 2109 ≤ primorial 1500 := by
  rw [primorial, filter_prime]
  decide +kernel

end ButheNumerics.v2.Dev
