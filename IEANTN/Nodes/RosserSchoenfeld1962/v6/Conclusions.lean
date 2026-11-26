/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Mathlib.NumberTheory.Chebyshev

/-! # Rosser–Schoenfeld 1962: Theorem 25, equation (5.3)

The definitions of ψ and θ on p. 64 include the upper endpoint, as in Mathlib.
-/

namespace RosserSchoenfeld1962.v6

/-- **Theorem 25, equation (5.3), p. 77.** For every real `x ≥ 1`,
`θ(x) ≤ ψ(x) < 1.2 a x + (3 log x + 5)(log x + 1)`, with the paper's exact
constant `a = (7/15) log 2 + (3/10) log 3 + (1/6) log 5`.
The lower inequality is non-strict, the upper one is strict, and the threshold
includes 1. The displayed decimal `1.2` is exactly `6/5`. -/
def theorem_25 : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    Chebyshev.theta x ≤ Chebyshev.psi x ∧
      Chebyshev.psi x <
        (6 / 5) * ((7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 +
          (1 / 6) * Real.log 5) * x + (3 * Real.log x + 5) * (Real.log x + 1)

end RosserSchoenfeld1962.v6
