/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Node `RosserSchoenfeld1962.v8`

Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*,
Illinois J. Math. **6** (1962), 64–94: the lower bound (3.19) in the Corollary to Theorem 5.

The sum runs over the primes `p ≤ x`, written as the primes in `Finset.Iic ⌊x⌋₊`. For `1 < x`
the floor is at least `1`, and `log x > 0`, so `log (log x)` is a genuine real logarithm rather
than a junk value; for `1 < x < 2` the sum is empty and the claim is `log (log x) < 0`.
-/

namespace RosserSchoenfeld1962.v8

/-- **Equation (3.19), Corollary to Theorem 5, p. 70.** `log log x < ∑_{p ≤ x} 1/p` for every
real `x > 1`.

The inequality is strict and the range is `1 < x`, as printed. The Corollary's other half,
(3.20), `∑_{p ≤ x} 1/p < log log x + B + 1/log² x`, is not represented here. This conclusion
matches the statement of PNT+'s `RS_prime.theorem_c` (up to writing `<` for `>`). -/
def equation_3_19 : Prop :=
  ∀ x : ℝ, 1 < x →
    Real.log (Real.log x) < ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (1 / (p : ℝ))

end RosserSchoenfeld1962.v8
