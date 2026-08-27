/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `FKS2Numerics.v1`

The finite numerical checks that `FKS2`'s corollaries rest on, separated from the analysis that
consumes them.

Same paper as `FKS2.v1` — Fiori, Kadiri and Swidinsky, *Sharper bounds for the error term in the
Prime Number Theorem* — but a different **kind** of claim, and that is the whole point of the
split. `FKS2.v1` carries analysis, justified by the paper's argument. This carries arithmetic on
bounded ranges, justified by a computation. Keeping them apart lets a consumer see which part of
its trust is analytic and which is a finite check somebody ran.

## Why this is its own node

Three reasons, in increasing order of how much they matter.

The evidence differs. A `numerical` justification records the outcome of a computation; a
`literature` one records an argument a referee read. Mixing them on one node makes the weaker of
the two invisible.

The `sorry`s go somewhere. `PrimeNumberTheoremAnd` threads these data through its FKS2 development
as deliberate holes — its own docstring notes that `#print axioms corollary_23_all` reports
`sorryAx` on their account. It has no choice: there is no import mechanism there. Here they become
**hypotheses**, so `FKS2.v1`'s solution can be free of `sorryAx` while resting on exactly the same
computations, stated where a reader can find them.

And it is what a pipelined `FKS2.v2` will need. A pipeline abstracts over the numerical input
rather than baking one paper's table into the argument; that is only possible if the input is a
separate importable claim to begin with.

## What is here, and what is not

Only what a stated `FKS2.v1` conclusion actually consumes. `FKS2.v1.corollary_23` states the
`[0.826, 0.25, 1.00, 1.000]` row of the paper's Table 6, which is its **row 2**, and the finite
check that row needs is the one below.

The paper's other Table 6 rows have their own floors, on their own windows, and its Table 7 has
another eleven; upstream states ten and twenty-five of them respectively. None is stated here,
because no conclusion in this network consumes one yet. Add them when something does — the shape
below is the pattern.
-/

namespace FKS2Numerics.v1

open IEANTN

/-- **Table 6, row 2: the small-`x` floor.** `Eπ(x) ≤ 0.826 (log x / R)^{1/4} exp(−(log x / R)^{1/2})`
for every `x` in `[e, e⁶]`, with `R = 5.5666305`.

That window is `x ∈ [2.72, 403]`, where the paper "checks directly for particularly small `x`":
`π(x)` is an exact prime count and `Li(x) = ∫₂ˣ dt / log t` a certified quadrature, so the claim is
bounded arithmetic with no analytic content. It is what pins the `x₀ = e` threshold of
`FKS2.v1.corollary_23`; above the window the asymptotic bound carries the argument on its own.

Stated on `Set.Icc`, a closed window, matching upstream. Note this is a *floor* — a claim about
small `x` — not a tail bound, so it does not compose with anything above `e⁶` by monotonicity and
a consumer must not assume it does. -/
def table6_row2_floor : Prop :=
  ∀ x ∈ Set.Icc (Real.exp 1) (Real.exp 6),
    Eπ x ≤ admissibleBound 0.826 0.25 1 5.5666305 x

end FKS2Numerics.v1
