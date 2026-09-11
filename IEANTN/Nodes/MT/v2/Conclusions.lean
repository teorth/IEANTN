/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastián Rodrigo (AI-assisted)
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `MT.v2`

Mossinghoff and Trudgian, *Nonnegative trigonometric polynomials and a zero-free region for the
Riemann zeta-function*, J. Number Theory **157** (2015), 329–349 — **§7, Corollary 1**, the
explicit bound on `θ(x) - x` that the classical zero-free region (`MT.v1.zero_free_region`)
converts into by the paper's own standard zero-free-region-to-`θ` recipe.

A **variant** of `MT.v1`, not a successor: `MT.v1` states the paper's two zero-free regions
(Theorem 1, §6.1); this node states its one further conclusion actually used elsewhere in this
network — Corollary 1 — as its own conclusion rather than folding it into `MT.v1`, so that a
consumer of one does not have to inherit the other's import.

## Why this node exists

`DudekPlattNumerics.v3`'s docstring already traces its `R = 6.315` to this exact corollary, but
could not cite it: `MT.v1` did not state Corollary 1, so the dependency was `traced` prose, not a
drawable edge. This node exists so `DudekPlattNumerics.v4` (and anything else wanting an explicit
`θ`-error bound at this `R`) can import it as `MT.v2.corollary_1` instead.

## What the paper actually proves, and what it consumes

Corollary 1's own proof (fetched and read directly from the open-access arXiv preprint
`arXiv:1410.3926`) reads: *"Theorem 1 can be used, as in [19, p. 2], to show that there are no
zeros … in the region `σ ≥ 1 - 1/(6.315 log|t/17|)`, `t ≥ 24`. The statement then follows
from the arguments in [19]"* — i.e. it repeats Trudgian's own (arXiv:1401.2689)
classical-region-to-`θ` conversion recipe verbatim, substituting `MT.v1.zero_free_region`'s own
`R₀ = 5.573412` for Kadiri's raw `5.69693`. So the only network input this conclusion needs
beyond ordinary calculus is `MT.v1.zero_free_region` itself — which already imports
`Platt2015.v1.rh_up_to`, the `T₀ = 3.06 · 10¹⁰` computationally-verified height Theorem 1
consumes. "Unconditional" for this corollary, as for `MT.v1.zero_free_region`, means that height
is *established*, not *absent*.

**Not proved here.** This conclusion is `literature`-justified, exactly like `MT.v1`'s own two:
the network cites the paper's Corollary 1 rather than re-deriving the zero-free-region-to-`θ`
conversion argument itself, which is genuine analytic work (a contour integral against the
zero-counting function) that no node in this network currently formalizes. A consumer importing
this conclusion is trusting Mossinghoff–Trudgian's proof, not a Lean derivation of it. -/

namespace MT.v2

open IEANTN Real

/-- **§7, Corollary 1.** For every `x ≥ 149`,

`|θ(x) - x| ≤ x · √(8/(17π)) · (log x / R)^{1/4} · exp(-√(log x / R))`, `R = 6.315`.

Spelled with the network's own normalised-error-term vocabulary: `Eθ x = |θ(x) - x| / x` obeys the
classical admissible bound `A (log x/R)^B exp(-C(log x/R)^{1/2})` at `A = √(8/17π)`, `B = 1/4`,
`C = 1`, `R = 6.315 = 1263/200`, above `x = 149`.

The paper's own Corollary 1 states this with `X := √(log x / R)` as `x√(8/17π) X^{1/2} e^{-X}`
— `X^{1/2} = (log x/R)^{1/4}` is exactly `HasClassicalBound`'s `(log x/R)^B` at `B = 1/4`, and
the bare `e^{-X}` is exactly its `exp(-C(log x/R)^{1/2})` at `C = 1`. `x ≥ 149` is the paper's
own stated range (Corollary 1's hypothesis, inherited from Theorem 1's `t ≥ 2` converted through
the same `x`-vs-`t` normalisation Trudgian's own recipe uses). -/
def corollary_1 : Prop :=
  HasClassicalBound Eθ (Real.sqrt (8 / (17 * Real.pi))) (1 / 4 : ℝ) 1 (1263 / 200 : ℝ) 149

end MT.v2
