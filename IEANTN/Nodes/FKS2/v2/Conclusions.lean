/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `FKS2.v2` — the pipeline form

Same paper as `FKS2.v1`, stated the other way round. `v1` is faithful to how Fiori, Kadiri and
Swidinsky present their results: named corollaries at named constants. This version states the two
**transformations** those corollaries are instances of.

`docs/NODES.md` is explicit that this is what versions are for: "Versions are *variants*, not a
succession: a `paper` version faithful to how a source states its result and a `pipeline` version
stating a more general form both earn their place permanently, and neither obsoletes the other."

## Why it is worth a version of its own

**Different evidence, different lifetime.** These two conclusions import *nothing*: quantified over
all admissible parameters, they consume no other result in the network, so a Lean proof is their
entire justification and they can be verified today. `FKS2.v1`'s corollaries cannot — they wait on
numerical inputs that neither this project nor `PrimeNumberTheoremAnd` has formalized, notably the
step-function interpolation below `e²⁰⁰⁰⁰` and the Table 4 transport.

Verification in this network is per node and all-or-nothing: `record-receipt` refuses unless the
solution's `comparator.json` covers every conclusion, precisely so that adding a conclusion to a
verified node cannot inherit its receipt. Keeping the pipelines on `v1` would therefore hold them
hostage to numerics they have nothing to do with.

**And it is what a later consumer wants.** A pipeline abstracts over the numerical input rather
than baking one paper's table into the argument. Point it at a better `ψ − θ` bound, or a better
`Eθ` bound, and it yields the corresponding improvement with nothing restated.

## The `ψ − θ` comparison is a hypothesis, not an import

Proposition 13 could have imported `BKLNW`'s coefficients. It takes the comparison as an internal
hypothesis instead, in the manner of `Lcm.v2`, so the pipeline stands alone and a user supplies
whichever bound they have. That is also what keeps its import list empty.

## Three hypotheses the paper does not state

`exp 1 ≤ x₀` on Proposition 13, and `C/(2√R) ≤ √(log x₀)` and `0 < C` on Theorem 3. Each is
documented at its statement. They were found here by formalizing, but they are **not new**:
`PrimeNumberTheoremAnd` already carries the same conditions, and for its `theorem_3` an explicit
note that they "are not present in the source material [FKS2]". Where this node does differ is that
Proposition 13 needs only `exp 1 ≤ x₀` where upstream requires `7 ≤ log x₀`, so this statement is
the stronger one.
-/

namespace FKS2.v2

open Real IEANTN

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

end FKS2.v2
