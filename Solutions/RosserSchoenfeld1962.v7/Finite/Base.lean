/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Num.Prime
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace RS39

/-- Mathlib's binary primality instance is designed for kernel reduction. -/
def fastCount (n : ℕ) : ℕ :=
  Nat.count (fun p : ℕ => Num.Prime (p : Num)) (n+1)

lemma fastCount_eq (n : ℕ) : fastCount n = Nat.primeCounting n := by
  simp [fastCount, Nat.primeCounting, Nat.primeCounting', Num.Prime]

/-- Soundness of a monotonicity block in the finite count certificate. -/
lemma range_bound {a b n : ℕ} (ha : a ≤ n) (hb : n ≤ b)
    (hc : (fastCount (2*b+1) - fastCount a) * (Nat.log 2 (b+1)+1) ≤ 2*a) :
    (Nat.primeCounting (2*n+1) - Nat.primeCounting n) * (Nat.log 2 (n+1)+1) ≤ 2*n := by
  simp only [fastCount_eq] at hc
  have h1 := Nat.monotone_primeCounting (show 2*n+1 ≤ 2*b+1 by omega)
  have h2 := Nat.monotone_primeCounting ha
  have h3 := Nat.log_mono_right (b := 2) (show n+1 ≤ b+1 by omega)
  have h4 : Nat.primeCounting (2*n+1) - Nat.primeCounting n ≤
      Nat.primeCounting (2*b+1) - Nat.primeCounting a := by omega
  exact (Nat.mul_le_mul h4 (Nat.add_le_add_right h3 1)).trans (hc.trans (by omega))

end RS39
