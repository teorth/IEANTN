/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# Node `ChebyshevNumerics.v2` — `ψ(x) ≤ 1.11 x`, with the threshold gone

One conclusion: `ψ(x) ≤ 1.11 x` for every real `x > 0`.

## Why this version exists

`ChebyshevNumerics.v1.psi_le_below_11723` says `ψ(n) ≤ 1.11 n` for integers `n ≤ 11723`. Both
restrictions — the threshold and the naturals — came from *how the claim was first obtained*, not
from what is known. The original ground was PrimeNumberTheoremAnd's `native_decide` evaluation of
an incremental checker, which ranges over integers up to a bound, and `11723` is where
`Chebyshev.v1.psi_upper_clean`'s induction takes over.

Since #231 the designated justification is instead a bridge from
`RosserSchoenfeld1962.v1.equation_3_35`, which is `ψ(x) < 1.03883 x` for **every** `x > 0` and
carries a Comparator receipt. That bridge introduces the hypothesis `n ≤ 11723` and never uses it.
So the network held evidence strictly stronger than the statement it was attached to, and a reader
meeting the node afterwards would read `11723` as a frontier when it is a fossil. Issue #253 is
that observation; this node is the answer to it.

## What is not changing

`ChebyshevNumerics.v1` stays exactly as it is, and stays `active`. `Chebyshev.v1.psi_upper_clean`
imports it in the `ℕ`-indexed finite shape its solution uses, and *strengthening* a conclusion a
consumer assumes would hand that consumer a stronger premise and so weaken its conditional theorem.
That is a degradation, not an improvement, which is why this is a new version rather than an edit
and why nothing is repointed here. A consumer that wants the unconditional form can migrate when it
suits it; until one does, `v1` is the one on the path and this is the honest statement of what the
network can actually support.

## Why `ℝ` and not `ℕ`

`v1` argued for `ℕ` on the grounds that the computation ranges over integers and a consumer wanting
the real form can take the monotonicity step itself. With the computation no longer the ground,
that argument goes with it: equation (3.35) is a statement about reals, so stating this one over
reals is what makes the bridge a weakening of the coefficient and nothing else. The `n = 0` case
and the `ℕ → ℝ` cast both disappear.

This node is **not** a computation. Nothing here is checked by evaluation; it is a corollary of a
published, Lean-verified bound, and its `kind` says so.
-/

namespace ChebyshevNumerics.v2

/-- **`ψ(x) ≤ 1.11 x` for every real `x > 0`.**

The unconditional form of `ChebyshevNumerics.v1.psi_le_below_11723`, which carried a threshold of
`11723` and quantified over `ℕ`. Neither restriction survives contact with the evidence: Rosser and
Schoenfeld's `ψ(x) < 1.03883 x` holds for all `x > 0`, so the only step between it and this is
`1.03883 ≤ 1.11`.

The `1.11` is kept rather than sharpened to `1.03883`. It is the constant
`Chebyshev.v1.psi_upper_clean` is stated with, and the point of this version is to remove an
artefact, not to introduce a second one — a node claiming `1.03883` would simply be
`RosserSchoenfeld1962.v1.equation_3_35` with a non-strict inequality, which is not worth a node.
A consumer needing the sharper constant should import that conclusion directly.

`x > 0` rather than `x ≥ 0`: at `x = 0` the claim is `ψ 0 ≤ 0`, which is true, but equation (3.35)
is stated on `x > 0` and widening the domain here would make the bridge prove something its source
does not say. -/
def psi_le_all : Prop :=
  ∀ x : ℝ, 0 < x → Chebyshev.psi x ≤ 1.11 * x

end ChebyshevNumerics.v2
