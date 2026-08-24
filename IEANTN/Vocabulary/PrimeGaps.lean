/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

/-!
# Vocabulary: primes in short intervals

The predicates in which Bertrand-type and Dusart-type results are stated.
-/

namespace IEANTN

open Real

/-- `HasPrimeInInterval x h`: there is a prime in the half-open interval `(x, x + h]`.

The interval is open at the left and closed at the right, matching the convention in Dusart and in
the Rosser–Schoenfeld literature.  A source stating `x ≤ p < x + h` is making a *different* claim
at the endpoints; transcribe carefully. -/
def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) ≤ x + h

/-- `HasPrimeInInterval.logPower X₀ k`: for every `x ≥ X₀` there is a prime in
`(x, x + x / (log x)^k]`.

This is the shape of Dusart's Proposition 5.4 (`k = 3`, `X₀ = 89693`) and of its successors.  The
exponent is a `Real.rpow`, so `k` need not be a natural number. -/
def HasPrimeInInterval.logPower (X₀ k : ℝ) : Prop :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x) ^ k)

end IEANTN
