/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import IEANTN.Vocabulary.PrimeCounting

/-! # Rosser–Schoenfeld 1962: primes in a doubled interval -/

namespace RosserSchoenfeld1962.v3

/-- Rosser–Schoenfeld 1962, Corollary 3, equation (3.8), p. 69.
For every real `x ≥ 20½`, the interval `(x, 2x]` contains more than `3x/(5 log x)`
primes. Both prime counts include their upper endpoint, and the inequality is strict. -/
def equation_3_8 : Prop :=
  ∀ x : ℝ, (41 : ℝ) / 2 ≤ x →
    3 * x / (5 * Real.log x) <
      IEANTN.primeCounting (2 * x) - IEANTN.primeCounting x

end RosserSchoenfeld1962.v3
