/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Prime.Basic

/-!
# Node `PrimesBetweenCubes.v1`

The explicit threshold for a prime between successive cubes recorded by Mossinghoff, Trudgian
and Yang as an application of their Korobov–Vinogradov region.

Read from arXiv:2212.06867, section "Some immediate applications": substituting their Theorem Main
into Cully-Hugill's argument with `α = 1/3 + 10^{-13}` gives a prime between `n³` and `(n+1)³`
for every integer `n ≥ exp(exp(32.76))`. Dudek's earlier threshold was `exp(exp(33.3))`;
Cully-Hugill's was `exp(exp(32.892))`. This node states only the threshold MTY records.
-/

namespace PrimesBetweenCubes.v1

/-- **A prime between successive cubes, from MTY's application of Theorem Main.**
For every integer `n ≥ exp(exp(32.76))` there is a prime strictly between `n³` and `(n+1)³`. -/
def prime_between_successive_cubes : Prop :=
  ∀ n : ℕ, Real.exp (Real.exp 32.76) ≤ n →
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3

end PrimesBetweenCubes.v1
