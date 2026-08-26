/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Vocabulary: the zeta function, its zeroes, and the shapes of estimates on them

The zeta-side vocabulary: the zero set, zero counting functions, and the three predicates in which
the literature's headline zeta results are stated — a verified height for the Riemann hypothesis,
a classical zero-free region, and a Riemann–von Mangoldt bound.
-/

namespace IEANTN

open Real

/-! ### The zero set -/

/-- The zero set of `ζ`, as a subset of `ℂ`.  This includes the trivial zeroes at the negative
even integers; restrict with `zeroesIn` when the intended set is the nontrivial zeroes. -/
def zetaZeroes : Set ℂ := {s : ℂ | riemannZeta s = 0}

/-- The zeroes of `ζ` in the rectangle `{Re s ∈ I, Im s ∈ J}`.

Taking `I = Set.Ioo 0 1` restricts to the critical strip, hence to the nontrivial zeroes. -/
def zetaZeroesIn (I J : Set ℝ) : Set ℂ :=
  {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zetaZeroes}

/-- The order of vanishing of `ζ` at `s`, as an integer; `0` away from zeroes and poles.

Used to count zeroes with multiplicity. -/
noncomputable def zetaOrder (s : ℂ) : ℤ := (meromorphicOrderAt riemannZeta s).untopD 0

/-- The sum of `f` over the zeroes of `ζ` in a rectangle, counted with multiplicity.

**Junk-value warning — read before using this in a statement.**  `tsum` returns `0` when the family
is not `Summable`, so a statement built from `zetaZeroesSum` can typecheck and be *vacuously* wrong
rather than false.  This bites in practice: a bare `∑_ρ f(s - ρ)` over the nontrivial zeroes is
typically **not** summable, because the terms carry a `f(0)/(s - ρ)` tail whose absolute sum
diverges even after the Riemann–von Mangoldt bound is applied.  The fix is to state the
pole-subtracted or paired form — `∑_ρ (f(0)/(s-ρ) - F(s-ρ))`, or `∑_ρ (1/ρ + 1/(s-ρ))` — whose
regularised packets genuinely are summable.  Whenever a node's conclusion contains a sum over
zeroes, establish summability first, or restate in regularised form. -/
noncomputable def zetaZeroesSum {α : Type*} [RCLike α] (I J : Set ℝ) (f : ℂ → α) : α :=
  ∑' ρ : zetaZeroesIn I J, f ρ * (zetaOrder ρ : ℤ)

/-! ### Zero counting functions -/

/-- `N T`, the number of zeroes of `ζ` with imaginary part in `(0, T)`, counted with
multiplicity. -/
noncomputable def zetaN (T : ℝ) : ℝ := zetaZeroesSum Set.univ (Set.Ioo 0 T) fun _ ↦ 1

/-- `N σ T`, the number of zeroes of `ζ` with real part in `(σ, 1)` and imaginary part in `(0, T)`,
counted with multiplicity.  The quantity bounded by a zero-density estimate. -/
noncomputable def zetaN' (σ T : ℝ) : ℝ := zetaZeroesSum (Set.Ioo σ 1) (Set.Ioo 0 T) fun _ ↦ 1

/-! ### The three headline predicates -/

/-- `RiemannHypothesisUpTo T`: `ζ` has no zeroes with real part in `(1/2, 1)` and imaginary part in
`[0, T]`.

This is the form in which a *numerical verification* of the Riemann hypothesis is recorded — Platt,
Gourdon–Wedeniwski, Platt–Trudgian.  Such a verification is a very large finite computation, so a
node asserting it will typically carry a `numerical` or `literature` justification rather than a
Lean solution. -/
def RiemannHypothesisUpTo (T : ℝ) : Prop :=
  IsEmpty (zetaZeroesIn (Set.Ioo (1 / 2) 1) (Set.Icc 0 T))

/-- `ClassicalZeroFreeRegion R t₀`: `ζ` has no zeroes with `Re s ≥ 1 - 1/(R log |Im s|)` and
`Im s ≥ t₀`.

`R` is the zero-free region parameter; smaller is stronger.  The chain of record values is
`5.573412` (Mossinghoff–Trudgian), `5.558691` (Mossinghoff–Trudgian–Yang), `4.896`
(Bellotti–Trudgian–Yang).

`t₀` is the height above which the region is claimed, and it is a parameter because the literature
has no consistent choice: Kadiri, Mossinghoff–Trudgian and Mossinghoff–Trudgian–Yang all state
`|t| ≥ 2`, Mossinghoff–Trudgian–Yang's Korobov–Vinogradov theorem states `|t| ≥ 3`, and
Rosser–Schoenfeld states `|t| ≥ 21` in a different shape entirely.  Fixing it at one value silently
weakened every node that used this definition; a smaller `t₀` is a *stronger* claim.

Only positive `t` is quantified over. Zeroes of `ζ` are symmetric about the real axis, so the
`|Im s|` form of the literature follows, but a consumer wanting negative `t` must do that step.

**Watch small `t₀`.** At `t = 1` the bound reads `1 - 1/(R * 0)`, and Lean's `1/0 = 0` makes it
`σ ≥ 1` — true but not what the formula suggests. For `t < 1`, `log t < 0` and the bound exceeds
`1`, so the claim says nothing. For `t` slightly above `1` the bound is hugely negative and the
claim is correspondingly strong. None of this is wrong, but `t₀ < 2` is not a region anybody has
stated, and a node claiming one should say why. -/
def ClassicalZeroFreeRegion (R t₀ : ℝ) : Prop :=
  ∀ σ t : ℝ, t₀ ≤ t → 1 - 1 / (R * log t) ≤ σ → riemannZeta (σ + t * Complex.I) ≠ 0

/-- The Riemann–von Mangoldt error shape `b₁ log T + b₂ log log T + b₃`. -/
noncomputable def rvmBound (b₁ b₂ b₃ T : ℝ) : ℝ :=
  b₁ * log T + b₂ * log (log T) + b₃

/-- `HasRvMBound b₁ b₂ b₃`: for all `T ≥ 2`,
`|N(T) - (T/2π) log(T/2πe) - 7/8| ≤ b₁ log T + b₂ log log T + b₃`.

Not every `N(T)` estimate in the literature fits this three-parameter shape — Trudgian's 2014
bound carries an extra `1/(5T)` term, for instance.  When a source's error term has a different
shape, a node should state it directly rather than force-fitting it here; forcing it changes the
theorem. -/
def HasRvMBound (b₁ b₂ b₃ : ℝ) : Prop :=
  ∀ T ≥ (2 : ℝ),
    |zetaN T - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤ rvmBound b₁ b₂ b₃ T

/-- A zero-density estimate: `N(σ,T) ≤ c₁(σ) T^{p(σ)} (log T)^{q(σ)} + c₂(σ) (log T)²` for
`T ≥ T₀` and `σ` in a given range.

This is a data-carrying structure rather than a predicate because the literature's zero-density
results differ in their admissible `σ` range and in all four coefficient functions, and downstream
consumers need to read those components back out.  It lives in Vocabulary rather than in any one
node precisely so that two nodes recording two different zero-density results produce values of the
*same* type and can therefore be compared and composed. -/
structure ZeroDensityBound where
  /-- The estimate holds for `T ≥ T₀`. -/
  T₀ : ℝ
  /-- The range of `σ` over which the estimate holds. -/
  σRange : Set ℝ
  /-- Coefficient of the main term. -/
  c₁ : ℝ → ℝ
  /-- Coefficient of the secondary `(log T)²` term. -/
  c₂ : ℝ → ℝ
  /-- Exponent of `T` in the main term. -/
  p : ℝ → ℝ
  /-- Exponent of `log T` in the main term. -/
  q : ℝ → ℝ
  /-- The estimate itself. -/
  bound : ∀ T ≥ T₀, ∀ σ ∈ σRange,
    zetaN' σ T ≤ c₁ σ * T ^ p σ * (log T) ^ q σ + c₂ σ * (log T) ^ 2

end IEANTN
