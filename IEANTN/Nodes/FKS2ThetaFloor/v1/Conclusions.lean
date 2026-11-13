/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.Numerics

/-!
# Node `FKS2ThetaFloor.v1`

`FKS2Numerics.v1.theta_asymp_ge_one_below_e30`, split out so a proof of this one statement is not
a receipt for the other four conclusions of that node.

The statement is the one already on `FKS2Numerics.v1`, including the closed interval and the
constants. Fiori, Kadiri and Swidinsky (*Sharper bounds for the error term in the Prime Number
Theorem*, the proof of Corollary 14) record that
`ε_{θ,asymp}(x) = A u³ exp(−2u)` for `u = √(log x / R)` rises to a maximum at `u = 3/2`, so on
`[2, e³⁰]` its minimum is at an endpoint. The paper's minimum is about `2.6271` at `x = 2`.
-/

namespace FKS2ThetaFloor.v1

open IEANTN

/-- **The small-range floor behind Corollary 14**, copied from
`FKS2Numerics.v1.theta_asymp_ge_one_below_e30`.

For every real `x` in the closed interval `[2, exp 30]`,
`1 ≤ margin 0 * admissibleBound 121.0961 (3 / 2) 2 5.5666305 x`. -/
def theta_asymp_ge_one_below_e30 : Prop :=
  ∀ x ∈ Set.Icc (2 : ℝ) (Real.exp 30),
    1 ≤ margin 0 * admissibleBound 121.0961 (3 / 2) 2 5.5666305 x

end FKS2ThetaFloor.v1
