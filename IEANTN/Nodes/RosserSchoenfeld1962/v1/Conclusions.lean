/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# Node `RosserSchoenfeld1962.v1`

Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*,
Illinois J. Math. **6** (1962), 64–94: the upper bound (3.35) in Theorem 12.

On p. 64 the paper defines `ψ(x)` as the logarithm of the least common multiple of the
positive integers `≤ x`, with value zero for `x < 2`. Mathlib's `Chebyshev.psi`, already used
by IEANTN's Vocabulary, has this same inclusive endpoint convention.
-/

namespace RosserSchoenfeld1962.v1

/-- **Equation (3.35), in Theorem 12, p. 71.** `ψ(x) < 1.03883 x` for every real `x > 0`.

Both the inequality and the positivity hypothesis are strict. Theorem 12 also asserts that
`ψ(x) / x` attains its maximum at `x = 113`; that separate assertion is not represented here.
This conclusion matches the bound proved by PNT+'s `RS_prime.theorem_12`. -/
def equation_3_35 : Prop :=
  ∀ x : ℝ, 0 < x → Chebyshev.psi x < 1.03883 * x

end RosserSchoenfeld1962.v1
