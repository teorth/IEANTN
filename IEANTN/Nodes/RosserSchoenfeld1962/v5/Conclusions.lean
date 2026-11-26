/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Mathlib.NumberTheory.Chebyshev

/-! # Rosser–Schoenfeld 1962: equation (5.4)

The definitions of ψ and θ on p. 64 include the upper endpoint, as in Mathlib.
-/

namespace RosserSchoenfeld1962.v5

/-- **Equation (5.4), p. 77.** `θ(x) < 1.11 x` for every positive real `x`.
The inequality is strict; the prime sum includes the upper endpoint, and `1.11`
denotes the exact rational `111 / 100`. -/
def equation_5_4 : Prop :=
  ∀ x : ℝ, 0 < x → Chebyshev.theta x < 1.11 * x

end RosserSchoenfeld1962.v5
