/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# Rosser–Schoenfeld 1962: the maximum clause of Theorem 12

Theorem 12 on p. 71 says that `ψ(x)/x` takes its maximum at `x = 113` and also gives
(3.35). The latter is represented separately by `RosserSchoenfeld1962.v1.equation_3_35`.
The printed maximum clause does not explicitly assert uniqueness; the second conclusion
below is a formally stronger formulation of the printed wording; no mathematical novelty is claimed.
-/

namespace RosserSchoenfeld1962.v2

/-- **Theorem 12, maximum clause.** Among positive real arguments, `ψ(x)/x` attains
its global maximum at 113. Mathlib includes each prime-power endpoint with full weight,
as does the paper's definition of `ψ` on p. 64. -/
def psi_ratio_maximum_at_113 : Prop :=
  ∀ x : ℝ, 0 < x →
    Chebyshev.psi x / x ≤ Chebyshev.psi (113 : ℝ) / 113

/-- **Explicit uniqueness refinement of Theorem 12's maximum clause.** The only positive real
argument attaining the maximum is 113. Uniqueness is not explicitly stated in the paper. -/
def psi_ratio_unique_maximum_at_113 : Prop :=
  ∀ x : ℝ, 0 < x →
    (Chebyshev.psi x / x = Chebyshev.psi (113 : ℝ) / 113 ↔ x = 113)

end RosserSchoenfeld1962.v2
