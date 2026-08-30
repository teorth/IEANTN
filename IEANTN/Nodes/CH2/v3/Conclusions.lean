/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.CH2.v2.Conclusions

/-!
# Node `CH2.v3`

The **extremal approximants** of Chirre–Helfgott, arXiv:2512.15709 §4, as replaced by the authors'
addendum *Replacement for Section 4.1*: band-limited majorants and minorants of the truncated
exponential, with their `L¹` error computed exactly.

A **variant** of `CH2.v2`, not a successor. `CH2.v2` is Proposition 2.4, which *consumes* such an
approximant as a hypothesis; this node *produces* one. Neither retires the other, and the two
compose: `v3` supplies exactly what `v2` assumes.

## Why the statements are existential

The approximant the paper constructs is an explicit function — a Beurling–Selberg-type combination
built from `z ↦ z coth(z/2)`, carrying a sign parameter and a shift. Naming it here would mean
putting that construction into a `Conclusions.lean`, where it would then be part of the statement of
record and every consumer would be pinned to the particular function rather than to its properties.

So these conclusions instead assert that an approximant **exists** with the four properties a
consumer actually uses. That keeps this file definition-free — it reuses `CH2.v2`'s `truncExp` and
`IsBandLimited` unchanged — and makes the conclusions directly consumable: the `∃ φ` can be fed
straight into `proposition_2_4_upper`'s `φ` with no bridging.

## The four properties, and why each is needed

`IsBandLimited φ β` and the majorant/minorant inequality are literally `CH2.v2`'s hypotheses.

`φ 0` is pinned because `CH2.v2.mainExpression` **evaluates `φ` at `0`** — an existential that did
not fix it would be useless downstream.

The `L¹` error is what makes the resulting bound *optimal* rather than merely true; it is the
quantity the paper minimises, and Corollary 1.2's `π/T` is its value.

The last two are consistent, and the check is worth recording: `∫ 𝓕 φ = φ 0` by Fourier inversion
and `∫ truncExp lambda = 1/|lambda|`, so the error must equal `φ 0 - 1/|lambda|`, which is what is
written. A transcription error in either would break that identity.

## The sign of `lambda`, which is where the port does not simply transfer

`CH2.v2` applies these at `lambda = 2π(σ - 1)/T`, and for `ψ` the relevant `σ` is `0`, so
**`lambda` is negative in the intended application**. `PrimeNumberTheoremAnd`'s development builds
its approximants for `Inu ν x = if 0 ≤ x then exp(-νx) else 0` with `ν > 0`, which is
`CH2.v2.truncExp` at *positive* argument only.

The two are related by reflection: for `ν > 0`,
`CH2.v2.truncExp (-ν) u = if u ≤ 0 then exp(νu) else 0`, which is `Inu ν (-u)`. Reflecting `φ`
reflects `𝓕 φ` and preserves support in `[-1, 1]`, so the negative case follows from the positive
one — but it is a step the upstream development does not take, because it never states the theorem
these approximants are for. See this node's limitations.

## The range of `β`

`β ≤ 2` is not cosmetic. The upstream decay estimate is `𝓕 φ = O(y^{-2})`, and
`IsBandLimited φ β` asks for `‖𝓕 φ y‖ ≤ C/|y|^β` at **every** `y ≠ 0`. For `|y| ≥ 1` a `y^{-2}`
bound implies a `y^{-β}` bound whenever `β ≤ 2`; for `|y| < 1` the requested bound exceeds `C`, and
`‖𝓕 φ‖ ≤ ‖φ‖₁` covers it. Above `β = 2` neither argument is available. `1 < β` is `CH2.v2`'s own
requirement, inherited.

## What `PrimeNumberTheoremAnd` has

`CH2_part1.lean` lines 1138–6472, the section *Extremal approximants to the truncated exponential*,
with **no `sorry`**. The three statements that matter are `CH2.Inu_bounds` (the majorant and
minorant inequalities), `CH2.varphi_fourier_plus_error` and `CH2.varphi_fourier_minus_error` (the
two `L¹` errors, in exactly the closed forms below).
-/

namespace CH2.v3

open Real MeasureTheory FourierTransform Complex

/-- **The extremal majorant.** For every non-zero `lambda` and every `β ∈ (1, 2]` there is a
function `φ` band-limited to `[-1, 1]` whose Fourier transform **majorizes** the truncated
exponential `truncExp lambda`, with `φ 0 = 1/(1 - e^{-|lambda|})` and `L¹` error exactly
`1/(1 - e^{-|lambda|}) - 1/|lambda|`.

This is the Graham–Vaaler extremal function, reconstructed self-containedly in the authors'
addendum. Its `L¹` error is optimal — no band-limited majorant does better — which is what makes
the `π/T` in Corollary 1.2 optimal rather than merely valid.

Imports nothing: `lambda` and `β` are universally quantified with their conditions as hypotheses, so
a Lean proof is this conclusion's whole justification, and it can be verified without waiting on any
numerical input.

Feeds `CH2.v2.proposition_2_4_upper` directly: the `φ` produced here satisfies that proposition's
`IsBandLimited` and majorant hypotheses verbatim. -/
def extremal_majorant : Prop :=
  ∀ lambda β : ℝ, lambda ≠ 0 → 1 < β → β ≤ 2 →
    ∃ φ : ℝ → ℂ,
      CH2.v2.IsBandLimited φ β ∧
      (∀ y : ℝ, CH2.v2.truncExp lambda y ≤ (𝓕 φ y).re) ∧
      φ 0 = ((1 / (1 - Real.exp (-|lambda|)) : ℝ) : ℂ) ∧
      ∫ y : ℝ, ((𝓕 φ y).re - CH2.v2.truncExp lambda y)
        = 1 / (1 - Real.exp (-|lambda|)) - 1 / |lambda|

/-- **The extremal minorant.** The same with the inequality reversed: `𝓕 φ` **minorizes**
`truncExp lambda`, with `φ 0 = 1/(e^{|lambda|} - 1)` and `L¹` error exactly
`1/|lambda| - 1/(e^{|lambda|} - 1)`.

Stated separately from the majorant rather than as a conjunction because the optimal majorant and
the optimal minorant are genuinely different functions — this is the same reason `CH2.v2` splits
Proposition 2.4 in two — so a consumer instantiates one or the other, not both at a shared `φ`.

Note the two `L¹` errors are **not** equal: `1/(1-e^{-λ}) - 1/λ` against `1/λ - 1/(e^λ - 1)`. They
differ by `1/(1-e^{-λ}) + 1/(e^λ - 1) - 2/λ`, which is positive; the majorant is the more expensive
side. That asymmetry is real and survives into the final constants.

Feeds `CH2.v2.proposition_2_4_lower`. -/
def extremal_minorant : Prop :=
  ∀ lambda β : ℝ, lambda ≠ 0 → 1 < β → β ≤ 2 →
    ∃ φ : ℝ → ℂ,
      CH2.v2.IsBandLimited φ β ∧
      (∀ y : ℝ, (𝓕 φ y).re ≤ CH2.v2.truncExp lambda y) ∧
      φ 0 = ((1 / (Real.exp |lambda| - 1) : ℝ) : ℂ) ∧
      ∫ y : ℝ, (CH2.v2.truncExp lambda y - (𝓕 φ y).re)
        = 1 / |lambda| - 1 / (Real.exp |lambda| - 1)

end CH2.v3
