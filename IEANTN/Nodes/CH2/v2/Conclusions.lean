/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Node `CH2.v2`

The Fourier-analytic core of Chirre–Helfgott, arXiv:2512.15709: **Proposition 2.4**, which converts
a band-limited majorant or minorant of the truncated exponential into a two-sided bound on
`∑_{n ≤ x} aₙ n^{-σ}`.

A **variant** of `CH2.v1`, not a successor. `CH2.v1` states the paper's numerical outputs for `ψ`;
this states the machinery they are obtained with, for an arbitrary non-negative Dirichlet
coefficient sequence. Both stay.

## Why this node and not the rest of the machinery

The paper has two analytic halves, and they are not equally suited to being nodes.

**This one is.** Proposition 2.4 is stated in Mathlib's own vocabulary — `Summable`, `Integrable`,
`𝓕`, `∑'`, `Set.Icc` — plus two small definitions of the paper's own, `partialSum` and
`truncExp` below. It imports nothing: every input is a hypothesis, so a Lean proof is its whole
justification.

**The contour-shifting half is not, at least not cheaply.** The paper's Proposition 5.2, which
`PrimeNumberTheoremAnd` also proves, is stated in terms of a ladder contour, admissible contours,
the Beurling–Selberg `Φ` family, and residue sums over regions — nine or more bespoke definitions.
Transcribing it faithfully would mean importing all of that into `IEANTN/Vocabulary/`, whose rule is
Mathlib-only definitions shared across the network. That is a real cost and should be a deliberate
decision, not a side effect. It is deferred; see this node's limitations.

## What `PrimeNumberTheoremAnd` has

`CH2_part1.lean`, 6472 lines with **no `sorry`**, containing exactly this proposition as
`CH2.prop_2_4_plus` and `CH2.prop_2_4_minus`, together with the Proposition 2.3 it rests on. So this
node is proved upstream and the work is a port, not a proof.

## The two conclusions are the same statement twice

`plus` assumes a *majorant* of the truncated exponential and yields an upper bound; `minus` assumes
a *minorant* and yields a lower bound. They are stated separately because a consumer generally has
only one of the two approximants to hand, and because the paper's optimal majorant and minorant are
different functions.
-/

namespace CH2.v2

open Real MeasureTheory FourierTransform Complex

/-- The partial sum the proposition bounds: `∑_{n ≤ x} aₙ n^{-σ}` for `σ < 1`, and the tail
`∑_{n ≥ x} aₙ n^{-σ}` otherwise.

Node-local, and the case split is the paper's own — the two regimes are genuinely different
objects, and `σ = 1` is excluded throughout. Follows `PrimeNumberTheoremAnd`'s `CH2.S`. -/
noncomputable def partialSum (a : ℕ → ℝ) (σ x : ℝ) : ℝ :=
  if σ < 1 then ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n : ℝ) ^ σ
  else ∑' n : ℕ, if (n : ℝ) ≥ x then a n / (n : ℝ) ^ σ else 0

/-- The truncated exponential `u ↦ e^{−λu}` on `λu ≥ 0` and `0` elsewhere.

This is the function whose optimal band-limited majorants and minorants Graham and Vaaler found,
and which the paper's addendum reconstructs self-containedly. Follows `PrimeNumberTheoremAnd`'s
`CH2.I'`, named to avoid the clash with `Complex.I`. -/
noncomputable def truncExp (lambda u : ℝ) : ℝ :=
  if 0 ≤ lambda * u then Real.exp (-lambda * u) else 0

/-- The coefficient hypothesis: non-negative, with `∑ |aₙ| / (n (log n)^β)` summable.

Non-negativity is what the whole method needs — it is why a majorant of the truncated exponential
gives an upper bound termwise. -/
def AdmissibleCoefficients (a : ℕ → ℝ) (β : ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧ Summable fun n : ℕ ↦ ‖(a n : ℂ)‖ / ((n : ℝ) * Real.log n ^ β)

/-- `G` is the Dirichlet series of `a` with its pole at `s = 1` removed, continuous up to the line
`Re s = 1` on the segment `|Im s| ≤ T`.

This is the finite spectral information the method consumes: the paper needs `G` only on that
segment, which is what lets it dispense with a zero-free region. -/
def IsPoleFreePart (a : ℕ → ℝ) (G : ℂ → ℂ) (T : ℝ) : Prop :=
  ContinuousOn G {z : ℂ | 1 ≤ z.re ∧ z.im ∈ Set.Icc (-T) T} ∧
    Set.EqOn G (fun s ↦ (∑' n : ℕ, (a n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1)) {z : ℂ | 1 < z.re}

/-- `φ` is band-limited to `[−1, 1]`, integrable, continuous at `0`, with Fourier transform decaying
like `|y|^{−β}`.

"Band-limited" is the constraint that makes the method work: `φ` supported on `[−1, 1]` means its
Fourier transform is entire of exponential type, and only the zeros below height `T` can matter. -/
def IsBandLimited (φ : ℝ → ℂ) (β : ℝ) : Prop :=
  Measurable φ ∧ Integrable φ ∧ ContinuousAt φ 0 ∧
    (∀ x, x ∉ Set.Icc (-1 : ℝ) 1 → φ x = 0) ∧
    ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β

/-- The right-hand side both halves of Proposition 2.4 compare `partialSum` against. -/
noncomputable def mainExpression (G : ℂ → ℂ) (φ : ℝ → ℂ) (T σ x : ℝ) : ℝ :=
  (((2 * Real.pi * (x ^ (1 - σ) : ℝ) / T) * φ 0).re
      + (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T,
          φ (t / T) * G (1 + t * Complex.I) * (x : ℂ) ^ (1 + t * Complex.I)).re)
    - if σ < 1 then 1 / (1 - σ) else 0

/-- **Proposition 2.4, the majorant half.** If `φ` is band-limited with
`truncExp (2π(σ−1)/T) y ≤ (𝓕 φ y).re` for every `y` — that is, `𝓕 φ` **majorizes** the truncated
exponential — then `partialSum a σ x` is at most `mainExpression`.

Imports nothing: `a`, `G`, `φ`, `T`, `β`, `σ` and `x` are all universally quantified and every
condition on them is a hypothesis. So a Lean proof is this conclusion's whole justification, and it
can be verified without waiting on any numerical input.

The direction is forced by `a ≥ 0`: majorizing the truncated exponential majorizes each term of the
sum, and non-negativity is what lets the termwise comparison survive summation. -/
def proposition_2_4_upper : Prop :=
  ∀ (a : ℕ → ℝ) (T β σ : ℝ) (G : ℂ → ℂ) (φ : ℝ → ℂ) (x : ℝ),
    AdmissibleCoefficients a β → 0 < T → 1 < β → σ ≠ 1 →
    IsPoleFreePart a G T → IsBandLimited φ β →
    (∀ y : ℝ, truncExp (2 * Real.pi * (σ - 1) / T) y ≤ (𝓕 φ y).re) →
    1 ≤ x →
      partialSum a σ x ≤ mainExpression G φ T σ x

/-- **Proposition 2.4, the minorant half.** The same with the inequality on `𝓕 φ` reversed — `𝓕 φ`
**minorizes** the truncated exponential — giving a lower bound on `partialSum`.

Stated separately rather than as a conjunction because the optimal majorant and the optimal minorant
are different functions, so a consumer instantiates this at a different `φ` from the one above. -/
def proposition_2_4_lower : Prop :=
  ∀ (a : ℕ → ℝ) (T β σ : ℝ) (G : ℂ → ℂ) (φ : ℝ → ℂ) (x : ℝ),
    AdmissibleCoefficients a β → 0 < T → 1 < β → σ ≠ 1 →
    IsPoleFreePart a G T → IsBandLimited φ β →
    (∀ y : ℝ, (𝓕 φ y).re ≤ truncExp (2 * Real.pi * (σ - 1) / T) y) →
    1 ≤ x →
      mainExpression G φ T σ x ≤ partialSum a σ x

end CH2.v2
