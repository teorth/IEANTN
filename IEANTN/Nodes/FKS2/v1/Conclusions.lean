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

## The two pipelines, now stated

**Proposition 13** (`Eψ → Eθ`) and **Theorem 3** (`Eθ → Eπ`) are the paper's reusable content, and
the reason this node's `kind` is `paper` rather than something narrower. They are now stated, below.

An earlier version of this docstring said they could not yet be stated faithfully, because
Proposition 13's conclusion names a multiplier built from Broadbent–Kadiri–Lumley–Ng–Wilk's `a₁`
and `a₂`, and writing that here would mean either duplicating BKLNW's definitions or inventing
them. It set out two routes: import BKLNW's coefficients, or carry the `ψ − θ` bound as an internal
hypothesis in the manner of `Lcm.v2`.

**Route 2 was taken**, and the reason is the one that docstring gave for preferring it: a pipeline
that stands alone is reusable, and a later `FKS2.v2` can re-point it at a better `ψ − θ` bound
without restating anything. It also means both pipelines import *nothing* — they are conditional
theorems about arbitrary parameters, so a Lean proof is their whole justification, and they can be
verified without waiting on any numerical input. The corollaries below are then instantiations.

The pipelines also carry three hypotheses the paper does not state; they are documented at the
statements. They were found here by formalizing, but they were **not new**:
`PrimeNumberTheoremAnd` already carries the same conditions, and for its `theorem_3` an explicit
note that they "are not present in the source material [FKS2]". The gap in the published paper is
real and independently confirmed; the credit for noticing it is not ours.

**Tables 6 and 7** are data. Corollary 23 asserts an admissible classical bound for every row of
Table 6 and Corollary 24 a bound for every row of Table 7; this node states the single row of
Table 6 that Corollary 26 rests on. The rest should follow once the tables live in Vocabulary as a
data structure, since a table is a different kind of object from a `Prop` and
`docs/ARCHITECTURE.md` puts data-carrying structures there.
-/

namespace FKS2.v1

open IEANTN

/-! ### The two pipelines

Proposition 13 and Theorem 3 are the paper's reusable content: they convert an admissible bound on
one error term into one on the next, for *any* parameters, and the corollaries are instantiations.
They are stated here with the `ψ − θ` comparison as an internal hypothesis rather than by importing
`BKLNW`'s coefficients — route 2 of the two the module docstring above sets out, chosen because a
pipeline that stands alone is what a later `FKS2.v2` can re-point at a better input.

Consequently **both import nothing.** They are conditional theorems about arbitrary parameters, so
their justification is a Lean proof and nothing else.

Three hypotheses below are **not in the paper**, and are not tidying:

* `exp 1 ≤ x₀` in Proposition 13. The `log x₀` factors in `ν_asymp` are spare only when
  `log x₀ ≥ 1`; below `e` the proposition is false. Take `x = x₀`, `a₁ = 1`, `a₂ = 0`.
* `C / (2√R) ≤ √(log x₀)` in Theorem 3. Its Lemma 12 discards the lower endpoint of an integral of
  `e^{v²}`, valid only when that endpoint is nonnegative; below it the discarded piece makes the
  bound go the wrong way.
* `0 < C`, which the monotonicity lemmas behind both need.

Each is recorded on this node's page. All three are also present in `PrimeNumberTheoremAnd`, which
found them first — see the attribution notes there. Where this node does differ is that
Proposition 13 needs only `exp 1 ≤ x₀` where upstream requires `7 ≤ log x₀`, so this statement is
the stronger one.
-/

/-- The Dawson function `D₊(x) = e^{-x²} ∫₀ˣ e^{t²} dt`.

Mathlib has no Dawson function, and Theorem 3 cannot be *stated* without one: substituting
`u = √(log t)` in the integral of an admissible bound and completing the square leaves an integral
of `e^{s²}`, and `D₊` is exactly that, rescaled. So `D₊` is what the `θ → π` constant is made of.

Lives here rather than in Vocabulary because only this node's conclusions mention it; promote it
when a second node needs it, as Vocabulary's own rule says. -/
noncomputable def dawson (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2) * ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2)

/-- The multiplier `ν_asymp` of the paper's (nu_asymp): how much an admissible bound for `Eψ` must
be inflated to serve for `Eθ`, given `ψ − θ ≤ a₁√x + a₂x^{1/3}`.

Transcribed verbatim, including the `log x₀` in each summand. Evaluating the paper's own (28) at
`x₀` gives the same expression *without* those factors, and `BKLNW`'s Corollary 5.1 has no
logarithm in it either, so this appears to be about `log x₀` times larger than the argument needs.
That is the safe direction — a larger `ν` is a weaker claim — so it is kept as printed and flagged
rather than tightened. It is also exactly why `exp 1 ≤ x₀` is needed. -/
noncomputable def nuAsymp (Aψ B C R a₁ a₂ x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / Real.log x₀) ^ B * Real.exp (C * Real.sqrt (Real.log x₀ / R)) *
    (a₁ * Real.log x₀ * x₀ ^ (-(1 : ℝ) / 2) + a₂ * Real.log x₀ * x₀ ^ (-(2 : ℝ) / 3))

/-- The correction `μ_asymp` of the paper's (mu_asymp_def).

First summand: the boundary term at `x₀`, normalised — which is why `π(x₀)` and `θ(x₀)` have to be
computable. Second: what the integral contributes, and where `D₊` reaches the final constant. -/
noncomputable def muAsymp (Aθ B C R x₀ x₁ : ℝ) : ℝ :=
  (x₀ * Real.log x₁) / (admissibleBound Aθ B C R x₁ * x₁ * Real.log x₀) *
      |(primeCounting x₀ - Li x₀) / (x₀ / Real.log x₀) - (Chebyshev.theta x₀ - x₀) / x₀|
    + 2 * dawson (Real.sqrt (Real.log x₁) - C / (2 * Real.sqrt R)) / Real.sqrt (Real.log x₁)

/-- **Proposition 13**, the `Eψ → Eθ` pipeline: an admissible bound for `Eψ` gives one for `Eθ`
with `A` inflated to `Aψ(1 + ν_asymp)` and `B`, `C`, `R`, `x₀` unchanged.

The conclusion names the constant. An existentially quantified version would typecheck and be
useless: Corollary 14 needs the actual number to get from `121.096` to `121.0961`.

`C²/(8R) < B` is the paper's, and the `8` is not a slip for `16`: the binding case is the
`g(1/2, …)` of its (28), where Lemma 10(a) at `a = 1/2` reads `-B < -C²/(8R)`. -/
def proposition_13 : Prop :=
  ∀ Aψ B C R a₁ a₂ x₀ : ℝ, 0 < R → 0 < Aψ → C ^ 2 / (8 * R) < B → Real.exp 1 ≤ x₀ →
    0 ≤ a₁ → 0 ≤ a₂ →
    (∀ x ≥ x₀, Chebyshev.psi x - Chebyshev.theta x
      ≤ a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3)) →
    HasClassicalBound Eψ Aψ B C R x₀ →
    HasClassicalBound Eθ (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x₀

/-- **Theorem 3**, the `Eθ → Eπ` pipeline.

Two things are easy to lose and both are load-bearing. The conclusion holds from a **second**
threshold `x₁`, not from `x₀`; stating it at `x₀` claims more than the paper proves. And `A_π` is
explicit, `(1 + μ_asymp(x₀, x₁)) A_θ`.

The `x₁` threshold is not arbitrary: `√(log x₁) ≥ 1 + C/(2√R)` is what puts
`√(log x) - C/(2√R)` past the maximum of `D₊`, so that the Dawson factor is decreasing. -/
def theorem_3 : Prop :=
  ∀ Aθ B C R x₀ x₁ : ℝ, 0 < R → max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B → 2 ≤ x₀ → 0 < Aθ →
    0 < C → C / (2 * Real.sqrt R) ≤ Real.sqrt (Real.log x₀) →
    max x₀ (Real.exp ((1 + C / (2 * Real.sqrt R)) ^ 2)) ≤ x₁ →
    HasClassicalBound Eθ Aθ B C R x₀ →
    HasClassicalBound Eπ ((1 + muAsymp Aθ B C R x₀ x₁) * Aθ) B C R x₁

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
