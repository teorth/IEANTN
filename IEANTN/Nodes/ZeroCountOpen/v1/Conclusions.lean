/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Doolan
-/
import IEANTN.Vocabulary.Zeta
import IEANTN.Nodes.ZeroCount.v1.Conclusions

/-!
# Node `ZeroCountOpen.v1`

The passage between the two zero-counting conventions: `ZeroCount.v1.zetaNClosed`, which counts
zeroes with `0 < Im ρ ≤ t` (Rosser's and Chirre–Helfgott's convention), and `IEANTN.zetaN`, which
counts `0 < Im ρ < T`.

`ZeroCount.v1`'s module docstring records why the two are equivalent for bounds of the
Riemann–von Mangoldt kind with **no loss of constant**, and why comparing them at a single height is
the wrong comparison. This node is the lemma it says nobody had written.

## The argument

The zeroes with `0 < Im ρ ≤ T` are finitely many, so those with `Im ρ < T` have ordinates bounded
away from `T`: there is `s₀ < T` with none in `(s₀, T)`. For every `s ∈ (s₀, T)` the two counts
then agree exactly, `zetaNClosed s = zetaN T`. A bound on `zetaNClosed` at those heights is a bound
on `zetaN T` against the main term and error at `s`, and letting `s ↑ T` with both continuous at
`T` gives the bound at `T`.

`ioc_bound_to_ioo` states that once, for an arbitrary main term `M` and error `B`. The other two
conclusions apply it to `ZeroCount.v1.rvm_error_bound`, with the source's constants and range: once
in its own shape and once as an `IEANTN.HasRvMBound`, which is the shape consumers of `zetaN` use.

## Why `rvm_error_small` has no counterpart here

`ZeroCount.v1.rvm_error_small` is strict, `|Q(t)| < 1`. The limit `s ↑ T` only delivers `≤ 1`, and
the strict form does not follow from the hypothesis alone: if `zetaN T = main(T) - 1` with a simple
zero at height exactly `T`, the closed count at every height satisfies `< 1` and the open count at
`T` does not. Excluding that needs the zeroes themselves, so the open form of the small-range bound
is left to a node that has them, rather than stated here in a weaker form.

## Imports

The finiteness comes from `ZetaZeroes.v1`: `finite_zeroes_on_compact` for a compact set missing the
pole, and `zeroes_off_axis_in_strip` to put the zeroes with `0 < Im ρ ≤ T` in such a set.
-/

namespace ZeroCountOpen.v1

open Real IEANTN

/-- **Bounds on the closed count transfer to the open count.** If `zetaNClosed t` is within `B t`
of `M t` at every height in `(t₀, T)`, and `M`, `B` are continuous at `T`, then `zetaN T` is within
`B T` of `M T`.

Only heights strictly below `T` are used, which is what makes the transfer lossless: the closed
count at `T` itself may exceed the open one by the multiplicity at height `T`, and is never
consulted. -/
def ioc_bound_to_ioo : Prop :=
  ∀ (M B : ℝ → ℝ) (t₀ T : ℝ), t₀ < T → ContinuousAt M T → ContinuousAt B T →
    (∀ t : ℝ, t₀ < t → t < T → |ZeroCount.v1.zetaNClosed t - M t| ≤ B t) →
    |zetaN T - M T| ≤ B T

/-- **`ZeroCount.v1.rvm_error_bound` in the open convention.** `|N(T) - main(T)| ≤ (1/5) log T + 2`
for `T ≥ 1`, with `N` counting `0 < Im ρ < T`. Same constants and the same range as the source. -/
def rvm_error_bound_open : Prop :=
  ∀ T : ℝ, 1 ≤ T → |zetaN T - ZeroCount.v1.rvmMain T| ≤ (1 / 5) * log T + 2

/-- **Rosser's bound as an `IEANTN.HasRvMBound`.** `b₁ = 1/5`, `b₂ = 0`, `b₃ = 2`.

The form a node built on `zetaN` imports. `HasRvMBound` asks only for `T ≥ 2`, so this is a
restriction of `rvm_error_bound_open`, kept separate so a consumer can cite it directly. -/
def hasRvMBound : Prop :=
  HasRvMBound (1 / 5) 0 2

end ZeroCountOpen.v1
