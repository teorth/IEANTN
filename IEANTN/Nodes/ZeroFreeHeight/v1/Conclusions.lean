/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `ZeroFreeHeight.v1`

A folklore step: the height above which a classical zero-free region is claimed can be lowered
almost to `1`, given any numerical verification of the Riemann hypothesis that reaches at least as
far as the old height.

## Why the network needs it

`ClassicalZeroFreeRegion R t₀` carries its height as a parameter, because the literature has no
consistent choice — Kadiri, `MT` and `MTY` state `|t| ≥ 2`, `MTY`'s Korobov–Vinogradov theorem
states `3`, and `Rosser–Schoenfeld` states `21` in a different shape entirely. A node consuming a
region therefore has to match whatever its source happened to state, or restate the work.

Nobody proves the low range analytically, because there is nothing to prove: below the first
nontrivial zero the strip is empty, and every verification of the Riemann hypothesis covers that
range a thousand times over. The step is used without comment throughout the literature, which is
what makes it folklore rather than a citation.

## What it costs

The threshold cannot go all the way to `1`. The region at height `t` is `σ ≥ 1 - 1/(R log t)`, and
`RiemannHypothesisUpTo` says only that there is no zero with `Re s ∈ (1/2, 1)` below the verified
height — it says nothing at `Re s = 1/2`, where the nontrivial zeroes actually live. So the
argument needs the region to stay strictly right of the critical line, which is `R log t₀ > 2`, or
`t₀ > exp (2 / R)`.

That is a mild constraint but not a vacuous one, and it is why the bound is a hypothesis rather
than a constant. For `R = 5.5666305`, the value the `FKS` chain uses, it permits `t₀ > 1.4324`; for
Bellotti–Trudgian–Yang's `R = 4.896` it permits only `t₀ > 1.5045`. A hardcoded `1.5` would have
covered the first and quietly failed the second.

To go below `exp (2 / R)` one needs the height of the first nontrivial zero — that no zero has
`0 < Im s < 14.134…` at all, not merely none off the critical line. That is a genuinely different
input, and a natural second conclusion for this node whenever something wants it.
-/

namespace ZeroFreeHeight.v1

open IEANTN

/-- **Lowering the height of a classical zero-free region.**

If `ζ` has a classical zero-free region with parameter `R` above height `t₁`, and the Riemann
hypothesis has been verified to some height `T ≥ t₁`, then the same region holds above any
`t₀ ≤ t₁` with `R log t₀ > 2`.

The proof is a case split with nothing hidden in it. Above `t₁` the given region applies. Below it,
`t` is under the verified height, so a zero there would have to lie on the critical line or right of
`Re s = 1`; the first is excluded by `R log t₀ > 2`, which keeps the region strictly right of
`Re s = 1/2`, and the second by the classical non-vanishing of `ζ` on `Re s ≥ 1`, which Mathlib has
as `riemannZeta_ne_zero_of_one_le_re`.

`t₀ ≤ t₁` is not needed — if `t₁ < t₀` every `t ≥ t₀` already exceeds `t₁` — but it is kept because
it states the direction the lemma is for, and the omitted case is trivial.

The constraint is written `exp (2 / R) < t₀` rather than the equivalent-looking `2 < R * log t₀`,
which would be a junk-value trap: Mathlib's `Real.log` satisfies `log (-x) = log x`, so
`2 < R * log t₀` is satisfied by suitable *negative* `t₀`, for which the conclusion quantifies over
heights the hypothesis says nothing about. In the `exp` form `1 < exp (2 / R) < t₀` comes for
free. -/
def classical_region_descends : Prop :=
  ∀ R t₀ t₁ T : ℝ, 0 < R → Real.exp (2 / R) < t₀ → t₀ ≤ t₁ → t₁ ≤ T →
    RiemannHypothesisUpTo T → ClassicalZeroFreeRegion R t₁ → ClassicalZeroFreeRegion R t₀

end ZeroFreeHeight.v1
