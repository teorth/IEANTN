/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcos Adriano, Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `FKS.v2`

Fiori, Kadiri and Swidinsky, *Sharper bounds for the Chebyshev function `ψ(x)`*,
J. Math. Anal. Appl. **527** (2023), Paper No. 127426.

`FKS.v1` with the two questions its module docstring left open settled, and settled in Lean rather
than in prose. Both conclusions below are the same mathematics as `FKS.v1`'s; what changes is that
the threshold is the paper's own, and that neither is asserted on the authority of the paper twice.

## What v1 left open, and what happened to it

**The threshold.** `FKS.v1.psi_classical_bound` claims the classical bound only from `x₀ = e³⁰`,
the threshold `FKS2` quotes in its proof of Corollary 14. `FKS2`'s remark on admissible bounds and
PrimeNumberTheoremAnd both give the same four parameters from `x₀ = 2`. The two are **equivalent**:
`x₀ = 2` trivially gives `x₀ = e³⁰`, and `IEANTN/Bridges/FKS/ThresholdTwo.lean` proves the
converse from Mathlib alone. On `[2, e³⁰]` the right-hand side never falls below `2.627…`, its
minimum at `x = 2`, while Mathlib's `Chebyshev.psi_le` already gives `Eψ x ≤ 2` — the argument
`FKS2` itself makes for `Eθ` right after quoting the bound. So this node states the stronger,
published threshold.

**The rescaling.** `FKS.v1`'s notes record that `psi_classical_bound` is *not* derivable from
`psi_bound_all_x` by rescaling: at `R = 5.5666305`, `9.22022 R^{3/2} = 121.09602174…` overshoots
the printed `121.096`, and `0.8476836 √R = 1.99999992…` falls short of the printed `2`, both in the
strengthening direction. True, and it is the wrong direction to test. **The paper derives the
all-`x` bound from the classical one**, and says so in the proof of Corollary 1.4: *"We now simply
verify that `121.096/5.5666305^{3/2} < 9.22022` to complete the result."* Those same two
inequalities, read the other way, are exactly what that derivation needs, and
`IEANTN/Bridges/FKS/ClassicalToAllX.lean` carries it out. So `psi_bound_all_x` is not a second
thing to take on trust: it follows from the classical bound, and no `margin` index is involved.

The consequence for the network is that this node rests on **one** citation rather than two, and
`FKS.v1.rescaled_A_exceeds_printed` and `FKS.v1.rescaled_C_is_short_of_two` — which record the two
inequalities as claims — turn out to be the arithmetic the derivation runs on.

## What is still taken on trust

Everything else. The classical bound itself is the paper's, resting on a zero-free region, a zero
density estimate and a verification height, and this node does not prove it; the bridges relate it
to `FKS.v1`'s form, they do not establish it. See `limitations` in `formalization.yaml` for the
full list of inputs, four of which are not network edges and cannot be.

## Numbering, now settled

The published version numbers the all-`x` bound **Corollary 1.4**, and has no Corollary 1.3; the
"Corollary 1.3" that `FKS2` cites is the arXiv v1 number, from a version whose constant was
`9.22106` rather than `9.22022`. The classical form with `A = 121.096` is not a numbered statement
in any version: it is established inside the proof of Corollary 1.4, and the largest "Bound on `A`"
in the table in the proof of Lemma 5.3 is that value.
-/

namespace FKS.v2

open IEANTN

/-- **The all-`x` bound** (published Corollary 1.4).

`Eψ(x) < 9.22022 (log x)^{3/2} exp(−0.8476836 √(log x))` for every `x > 2`.

Identical to `FKS.v1.psi_bound_all_x`, and kept in the paper's own normalisation so the
transcription can be checked against the printed statement by eye. What changed is its standing:
it is `bridged` from `psi_classical_bound` below rather than cited, because that is the direction
the paper's own proof runs. -/
def psi_bound_all_x : Prop :=
  ∀ x > (2 : ℝ), Eψ x < 9.22022 * (Real.log x) ^ ((3 : ℝ) / 2) *
    Real.exp (-0.8476836 * Real.sqrt (Real.log x))

/-- **The classical bound, from the paper's own threshold** `x₀ = 2`.

`Eψ x ≤ 121.096 (log x / R)^{3/2} exp(−2 √(log x / R))` for every `x ≥ 2`, with `R = 5.5666305`.

`FKS.v1.psi_classical_bound` is this statement from `x₀ = e³⁰`, the threshold `FKS2` quotes when it
consumes the bound. The two are equivalent — see the module docstring — so nothing is claimed here
that `FKS.v1` did not already claim; the gain is that a consumer needing the bound below `e³⁰`, as
`FKS2`'s own remark does, no longer has to reprove the gap.

`R` is Mossinghoff and Trudgian's zero-free region constant, not this paper's; `MTY.v1` has a
sharper one, and it is the first thing to change when the chain is re-run. -/
def psi_classical_bound : Prop :=
  HasClassicalBound Eψ 121.096 (3 / 2) 2 5.5666305 2

end FKS.v2
