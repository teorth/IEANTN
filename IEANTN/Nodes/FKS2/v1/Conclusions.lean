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

This node exports four of the outputs. They are the results a downstream node can use without
knowing anything about how the paper works, which is what makes them the obvious things to state
first. All four are `lean-comparator` verified: the step from their imports to their statements is
proved in Lean at `Solutions/FKS2.v1` and was accepted by Comparator.

## The two pipelines live on `FKS2.v2`

**Proposition 13** (`Eψ → Eθ`) and **Theorem 3** (`Eθ → Eπ`) are the paper's reusable content, and
the corollaries below are instances of them. They were briefly stated here and have moved to
`FKS2.v2`, the pipeline variant — see `docs/NODES.md` on versions as variants rather than a
succession.

The move is not cosmetic. Verification here is per node and all-or-nothing — `record-receipt`
refuses unless `comparator.json` covers every conclusion — so keeping the pipelines here would have
held them hostage to the numerical inputs below, which they have nothing to do with and which
neither this project nor `PrimeNumberTheoremAnd` has formalized. Those inputs are now imported from
`FKS2Numerics.v1`, where they are asserted rather than proved, which is what lets the corollaries
below be verified as *conditional* theorems.

The corollaries now **import** them, which is what the network is for.

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

/-- **Corollary 22**, the paper's headline asymptotic bound:
`|π(x) − Li(x)| ≤ 9.2211 x √(log x) exp(−0.84768363 √(log x))` for all `x ≥ 2`.

Stated in the network's vocabulary at `R = 1`, which is the same claim:
`HasClassicalBound Eπ A B C 1` unwinds to `Eπ(x) ≤ A (log x)^B exp(−C √(log x))`, and multiplying by
`x / log x` gives the paper's displayed form exactly, with `B = 3/2` supplying the `√(log x)`.

`R` is folded into the constants rather than carried: the paper's own proof runs at
`R = 5.5666305`, and `121.107 / R^{3/2} = 9.22106…` and `2 / √R = 0.84768363…` are where the two
printed constants come from. Note the printed `C` is very slightly *below* `2/√R`, which is the
safe direction — a smaller `C` is a weaker bound.

This is what dominates Table 6's rows far out, and so what `corollary_23`'s tail rests on. -/
def corollary_22 : Prop :=
  HasClassicalBound Eπ 9.2211 (3 / 2) 0.84768363 1 2

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
