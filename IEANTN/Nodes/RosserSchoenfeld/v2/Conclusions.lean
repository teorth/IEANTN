/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.NumberTheory.Chebyshev

/-!
# Node `RosserSchoenfeld.v2`: the `b = 23` Chebyshev-psi bound

Rosser and Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x)*,
Math. Comp. **29** (1975), 243–269, Lemmas 7–9 and Theorem 4.

This node records the strict `0.00020211` bound at the threshold `exp 23`, conditional on
verification of RH through height `1894439`. The finite-RH statement is an explicit hypothesis,
not a verified conclusion of this node. In particular, this does not assert an unconditional
prime-number theorem or the smaller constant in Schoenfeld's 1976 refinement.

The external Lean proof uses fourfold polynomial smoothing, with a certified 29-zero head and
eight cancellation subbands. This adapts the paper's method rather than reproducing its 57-zero
head computation. It has no quantitative zero-free-region, Büthe, or Ramaré premise.
-/

namespace RosserSchoenfeld.v2

/-- The `b = 23` psi bound, with finite RH through the inclusive height `1894439` supplied
by the consumer. Both the threshold and the strict error inequality are retained. -/
def psi_error_b23 : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894439 →
    ∀ x : ℝ, Real.exp 23 ≤ x → |Chebyshev.psi x - x| < 0.00020211 * x

end RosserSchoenfeld.v2
