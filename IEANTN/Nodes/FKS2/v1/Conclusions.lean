/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `FKS2.v1`

Fiori, Kadiri and Swidinsky, *Sharper bounds for the error term in the prime number theorem*,
Res. Number Theory **9** (2023), Paper No. 63.

The paper has two halves. Its **machinery** is a pair of conversion pipelines: one carrying an
admissible classical bound on `Eψ` to one on `Eθ`, and one carrying a bound on `Eθ` to one on `Eπ`.
Its **output** is a set of explicit numerical bounds obtained by feeding the best available inputs
through those pipelines.

This node currently exports three of the outputs. They are the results a downstream node can use
without knowing anything about how the paper works, which is what makes them the obvious things to
state first.

## What is deliberately not stated yet

**The two pipelines** — Proposition 13 (`Eψ → Eθ`) and Corollary 21 (`Eψ → Eπ`) — are the paper's
reusable content and the reason this node's `kind` is `paper` rather than something narrower. They
are not here because they cannot yet be stated faithfully. Proposition 13's conclusion names the
multiplier

`ν_asymp(x₀) = (1/Aψ) (R / log x₀)^B exp(C √(log x₀ / R)) (a₁(log x₀) log x₀ x₀^(-1/2) + a₂(log x₀) log x₀ x₀^(-2/3))`

where `a₁` and `a₂` are Broadbent–Kadiri–Lumley–Ng–Wilk's bounds on `ψ − θ`. Writing that here
would mean either duplicating BKLNW's definitions into this node or inventing them, and stating the
pipeline with the multiplier existentially quantified instead would throw away the explicit constant
that is the entire point of the paper.

Two honest routes, in the order they should be tried:

1. give `BKLNW.v1` a conclusion bounding `ψ − θ`, promote `a₁` and `a₂` to Vocabulary, and state
   Proposition 13 against them — the pipeline then *imports* BKLNW, which is what the network is
   for;
2. or state Proposition 13 with the `ψ − θ` bound as an internal hypothesis, in the manner of
   `Lcm.v2`, so that the pipeline stands alone and a user supplies whichever bound they have.

Route 2 is more reusable and route 1 is more faithful to how the paper reads. That choice is worth
making deliberately rather than by default, and it wants someone who has read both papers.

**Tables 6 and 7** are data. Corollary 23 asserts an admissible classical bound for every row of
Table 6 and Corollary 24 a bound for every row of Table 7; this node states the single row of
Table 6 that Corollary 26 rests on. The rest should follow once the tables live in Vocabulary as a
data structure, since a table is a different kind of object from a `Prop` and
`docs/ARCHITECTURE.md` puts data-carrying structures there.
-/

namespace FKS2.v1

open IEANTN

/-- **Corollary 14.** The first Chebyshev error term obeys the admissible classical bound with
parameters `A = 121.0961`, `B = 3/2`, `C = 2`, `R = 5.5666305`, for all `x ≥ 2`.

`R = 5.5666305` is the zero-free region parameter the paper works with throughout; it comes from
the region it takes as input, not from this corollary. A node supplying a different region produces
a different `R`, which is why the pipelines above are the more valuable export. -/
def corollary_14 : Prop :=
  HasClassicalBound Eθ 121.0961 (3 / 2) 2 5.5666305 2

/-- **Corollary 23, at the row `[0.826, 0.25, 1.00, 1.000]` of Table 6.** The prime-counting error
term obeys the admissible classical bound with `A = 0.826`, `B = 0.25`, `C = 1`, `R = 5.5666305`,
for all `x ≥ e`.

Table 6 has many rows, trading `A` against the threshold; this is the one Corollary 26 rests on.
The others are equally true and equally exportable, and should be added as conclusions when a
downstream node wants them — or all at once, if the table is promoted to Vocabulary.

The threshold is `exp 1.000`, not `1.000`: Table 6's fourth column records `log x₀`. Transcribing
it as a bound on `x` rather than on `log x` would be a silent and enormous weakening. -/
def corollary_23 : Prop :=
  HasClassicalBound Eπ 0.826 0.25 1 5.5666305 (Real.exp 1)

/-- **Corollary 26.** `|π(x) − Li(x)| ≤ 0.4298 · x / log x` for every `x ≥ 2`.

The paper's headline unconditional estimate, and the one most likely to be cited on its own. Note
that the comparison is against the *offset* logarithmic integral `Li`, not `li`; the two differ by
`li 2 ≈ 1.045`, which is far from negligible at this precision. The Vocabulary docstring for `Eπ`
records the same warning.

The paper obtains this by combining Corollary 23 above `10¹⁹` with Büthe's estimates below it and
direct checks on small `x`, so a future `Buthe` node is a natural import once this conclusion is
justified by anything other than the paper's authority. -/
def corollary_26 : Prop :=
  HasNumericalBound Eπ 0.4298 2

end FKS2.v1
