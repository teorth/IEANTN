/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Node `GammaAsymptotics.v1`

Growth of the Gamma function and its logarithmic derivative — textbook asymptotics that Mathlib
happens not to have, stated once so that several nodes can import them.

At present there is one conclusion: `ψ(w) = log w + O(1/|w|)` in the right half-plane, the first
term of the Stirling expansion for the digamma function.

## Why this is a node and not a lemma inside a solution

Mathlib's `Analysis/SpecialFunctions/Gamma/Digamma.lean` is **sixty-four lines** — the definition
`digamma = logDeriv Gamma`, three special values, the recurrence `ψ(s+1) = ψ(s) + 1/s`, and
meromorphy. There is no bound on `ψ` anywhere in the library, and `Stirling.lean` concerns `n!`
rather than `Γ` in the complex plane.

That gap is not specific to any one paper. It is reached from any explicit estimate that shifts a
contour into the left half-plane, because the functional equation for `ζ` turns `ζ'/ζ(s)` into
`log 2π + (π/2)cot(πs/2) - ψ(1-s) - ζ'/ζ(1-s)` and the `ψ` term is what has to be controlled. The
first consumer here is `CH2.v1`, which needs it to bound `ζ'/ζ` on a ladder; it will not be the
last, and it is a plausible eventual contribution to Mathlib — though presumably with a different
proof from whatever first discharges it here.

## The shape of the statement

`ψ(w) - log w = O(1/|w|)` on `Re w ≥ 1`, with the constant existentially quantified rather than
named. That is deliberate. The sharp form is

  `ψ(w) = log w - 1/(2w) + O(1/w²)`,

and a consumer wanting the `-1/(2w)` term should state *that* rather than sharpening this; but no
consumer so far needs better than `O(1/|w|)`, and an explicit constant would invite exactly the
kind of numerology this node exists to avoid. `Re w ≥ 1` rather than a sector `|arg w| ≤ π - δ`
for the same reason: the half-plane is what the applications use, and the sector version is a
different statement that can join it here when wanted.

Note this immediately gives `‖ψ w‖ ≤ ‖log w‖ + C` and hence the `O(log|w|)` bound that a ladder
argument actually consumes.
-/

namespace GammaAsymptotics.v1

open Complex

/-- **The digamma function is `log w` up to `O(1/|w|)` in the right half-plane.**

The leading term of the Stirling expansion for `ψ = Γ'/Γ`. Standard, and stated here because
Mathlib carries no growth bound for `digamma` at all.

The constant is existential: the sharp statement is `ψ(w) = log w - 1/(2w) + O(1/w²)`, and a
consumer needing that should state it rather than sharpen this one.

Imports nothing: `w` is universally quantified with its condition as a hypothesis, so a Lean proof
is this conclusion's whole justification. -/
def digamma_sub_log_isBigO : Prop :=
  ∃ C : ℝ, ∀ w : ℂ, 1 ≤ w.re → ‖Complex.digamma w - Complex.log w‖ ≤ C / ‖w‖

end GammaAsymptotics.v1
