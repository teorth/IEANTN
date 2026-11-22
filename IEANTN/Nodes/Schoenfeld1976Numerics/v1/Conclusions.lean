/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Vocabulary.Zeta
import IEANTN.Nodes.ZetaZeroLocations.v1.Conclusions
import Mathlib.NumberTheory.Chebyshev

/-!
# Node `Schoenfeld1976Numerics.v1`: the `b = 23` entry of Schoenfeld's 1976 table

L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp.
**30** (1976), 337–360.

On printed p. 353 Schoenfeld says that he has recalculated the table of Section 5 of
Rosser–Schoenfeld (1975). The recalculated table is on printed p. 358, and its row `b = 23` reads
`m = 4`, `δ = 2.11 (-5)`, `ε = 2.0171 (-4)`. A row says `|ψ(x) − x| < ε x` for `x ≥ e^b`: that
is how the proof of Theorem 7* on printed p. 357 uses it ("If `e²² ≤ x < e²³`, we apply the table
to get `|ψ(x) − x| < 2.9941 · 10⁻⁴ x`", the row `b = 22`). The paper assumes
the Riemann hypothesis for the first `3 502 500` zeros, which Rosser and Schoenfeld use at the
height `A = 1894438.51224…`; as in `RosserSchoenfeld.v2`, the conclusion keeps that assumption as
an explicit premise, at `A` rounded down.

Same paper as `Schoenfeld1976.v1` (Theorem 11 and Theorem 7*), different kind of claim: a row of
the numerical table, which Theorem 7* uses (printed p. 357: "the table for `b = 23`"). Kept apart so
that it can be verified on its own, as `DudekPlattNumerics` is kept apart from `DudekPlatt`.

## The imports

The conclusion imports `ZetaZeroLocations.v1`: the zeros below height 1000. That is what the Lean
proof in `Solutions/Schoenfeld1976Numerics.v1` uses, with the same quartic smoothing and the same
`δ = 2.11 · 10⁻⁵` as the table row. Schoenfeld (printed pp. 352–353) used instead the first
12 555 zeros, from Lehman's computation, for `b ≥ 20`.
-/

namespace Schoenfeld1976Numerics.v1

/-- **Table on printed p. 358, row `b = 23`.** `|ψ(x) − x| < 0.00020171 x` for `x ≥ e^23`, with
the Riemann hypothesis up to `1894438.5122` supplied by the consumer. -/
def psi_error_b23 : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 →
    ∀ x : ℝ, Real.exp 23 ≤ x → |Chebyshev.psi x - x| < 0.00020171 * x

end Schoenfeld1976Numerics.v1
