/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.Numerics

/-!
# Node `FKS2PiFloor.v1`

The small-range floor behind Table 6, row 2 of Fiori, Kadiri and Swidinsky,
*Sharper bounds for the error term in the Prime Number Theorem*, Sections 5.2–5.3.

This is exactly `FKS2Numerics.v1.table6_row2_floor`, separated so verification of this
one conclusion does not certify the other four numerical conclusions of that node.
The vocabulary's `Li` is the offset integral from `2`, not principal-value `li`.
-/

namespace FKS2PiFloor.v1

open IEANTN

/-- **Table 6, row 2, small-range floor.** For every real `x` in the closed interval
`[exp 1, exp 6]`, the normalized prime-counting error is bounded by the row's curve,
with the original constants and the explicit, unchanged `margin 0` factor. -/
def table6_row2_floor : Prop :=
  ∀ x ∈ Set.Icc (Real.exp 1) (Real.exp 6),
    Eπ x ≤ margin 0 * admissibleBound 0.826 0.25 1 5.5666305 x

end FKS2PiFloor.v1
