/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.ChebyshevNumerics.v2.Conclusions
import IEANTN.Nodes.RosserSchoenfeld1962.v1.Conclusions

/-!
# Bridge: `ψ(x) ≤ 1.11 x` follows from equation (3.35)

`RosserSchoenfeld1962.v1.equation_3_35` is `ψ(x) < 1.03883 x` for every `x > 0`, and it has a
Comparator receipt. `ChebyshevNumerics.v2.psi_le_all` is the weaker unconditional statement
`ψ(x) ≤ 1.11 x` on the same domain.

All that separates them is `1.03883 ≤ 1.11` and one strict-to-non-strict step. Compare
`FromEquation335.lean`, the same bridge onto `v1`, which additionally has to dispose of `n = 0`
and cast `ℕ → ℝ`: those two cases were artefacts of `v1`'s shape, not of the mathematics, and
their absence here is the point of the new version. See #253.

This does not reprove equation (3.35).
-/

namespace IEANTN.Bridges.ChebyshevNumerics

theorem psi_le_all_of_equation_3_35
    (h : RosserSchoenfeld1962.v1.equation_3_35) :
    ChebyshevNumerics.v2.psi_le_all := by
  intro x hx
  have hlt : Chebyshev.psi x < 1.03883 * x := h x hx
  nlinarith [hlt, hx.le]

end IEANTN.Bridges.ChebyshevNumerics
