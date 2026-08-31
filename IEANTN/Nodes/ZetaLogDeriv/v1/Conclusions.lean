/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Node `ZetaLogDeriv.v1`

Identities and estimates for `ζ'/ζ` — the objects an explicit estimate reaches for when it shifts a
contour, stated once rather than rebuilt in each solution.

At present one conclusion: the functional equation, in logarithmic-derivative form.

## Why a node

`ζ'/ζ` is where explicit analytic number theory spends most of its effort, and Mathlib supplies its
two ends without the middle. It has the functional equation for `ζ` itself
(`riemannZeta_one_sub`) and the Dirichlet series `−ζ'/ζ(s) = ∑ Λ(n)n^{-s}` on `Re s > 1`
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, with `LSeriesSummable_vonMangoldt`). What it does
not have is the functional equation *differentiated*, which is what carries information about
`ζ'/ζ` from the convergent half-plane into the left one — and that is the step every ladder or
contour-shift argument needs.

That is not specific to one paper, which is why it is a node rather than a lemma inside
`Solutions/CH2.v1`. The same identity appears in Chirre–Helfgott as equation `(guruno)`, in their
`lem:derivbound`, written for `Ã = A` with its pole subtracted.

## The orientation is Mathlib's, not the textbook's

The identity is usually written

`ζ'/ζ(s) = log 2π + (π/2)cot(πs/2) − ψ(1−s) − ζ'/ζ(1−s)`,

which comes from the `sin`/`Γ(1−s)` form of the functional equation. **Mathlib has no
`Complex.cot`**, and its `riemannZeta_one_sub` is stated the other way round, as
`ζ(1−s) = 2(2π)^{-s} Γ(s) cos(πs/2) ζ(s)`. Differentiating *that* gives the equivalent

`ζ'/ζ(s) = −ζ'/ζ(1−s) + log 2π − ψ(s) + (π/2)tan(πs/2)`,

with `tan` and `ψ(s)` in place of `cot` and `ψ(1−s)`. The two are the same identity; this node
states the second because it is the one whose ingredients all exist. A consumer who wants the
`cot` form should state it separately rather than reshape this.

**Checked numerically before being written**, to 30 digits at five points including
`s = −3 + 2i` in the left half-plane, because a sign error here would be invisible to the
type-checker and fatal downstream.

## What is not here

No growth bound. `‖ζ'/ζ(s)‖ = O(log|s|)` on lines avoiding the zeros is the other half of what a
ladder argument wants, and it follows from this identity together with a digamma bound
(`GammaAsymptotics.v1`) and boundedness on `Re s ≥ 2` (a short consequence of the Dirichlet
series). It is not stated here because its clean form depends on which lines are chosen; when a
second consumer wants the same lines, that is the moment to add it.
-/

namespace ZetaLogDeriv.v1

open Complex

/-- **The functional equation in logarithmic-derivative form.**

`ζ'/ζ(s) = −ζ'/ζ(1−s) + log 2π − ψ(s) + (π/2)tan(πs/2)`.

The hypotheses are what make each term meaningful: `s ∉ {0, −1, −2, …}` and `s ≠ 1` are
`riemannZeta_one_sub`'s own, the first also keeping `ψ(s)` off its poles; the two non-vanishing
conditions make the logarithmic derivatives finite; and `cos(πs/2) ≠ 0` keeps `tan` off its poles,
which is exactly the odd integers.

Imports nothing: `s` is universally quantified with every condition a hypothesis, so a Lean proof
is this conclusion's whole justification. -/
def logDeriv_functional_equation : Prop :=
  ∀ s : ℂ, (∀ n : ℕ, s ≠ -n) → s ≠ 1 →
    riemannZeta s ≠ 0 → riemannZeta (1 - s) ≠ 0 → Complex.cos (Real.pi * s / 2) ≠ 0 →
      deriv riemannZeta s / riemannZeta s
        = -(deriv riemannZeta (1 - s) / riemannZeta (1 - s))
          + Complex.log (2 * Real.pi) - Complex.digamma s
          + (Real.pi / 2) * Complex.tan (Real.pi * s / 2)

end ZetaLogDeriv.v1
