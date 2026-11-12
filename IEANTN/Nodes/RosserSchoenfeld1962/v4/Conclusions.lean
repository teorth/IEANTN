/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Mathlib.NumberTheory.Chebyshev

/-! # Rosser–Schoenfeld 1962: Theorem 13: maximum at 361 and equation (3.36)

The definitions of ψ and θ on p. 64 include the upper endpoint, as in Mathlib.
-/

namespace RosserSchoenfeld1962.v4

/-- **Theorem 13, maximum clause, p. 71.** On the positive real axis,
`(ψ(x) - θ(x)) / √x` attains its global maximum at 361. This asserts attainment,
without adding uniqueness. Both Chebyshev functions include their upper endpoint. -/
def psi_sub_theta_ratio_maximum_at_361 : Prop :=
  ∀ x : ℝ, 0 < x →
    (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x ≤
      (Chebyshev.psi 361 - Chebyshev.theta 361) / Real.sqrt 361

/-- **Equation (3.36), p. 71.** For every positive real `x`, the difference
`ψ(x) - θ(x)` is strictly less than `1.42620 √x`. The decimal denotes the exact
rational `7131 / 5000`, not a floating-point approximation. -/
def equation_3_36 : Prop :=
  ∀ x : ℝ, 0 < x →
    Chebyshev.psi x - Chebyshev.theta x < 1.42620 * Real.sqrt x

end RosserSchoenfeld1962.v4
