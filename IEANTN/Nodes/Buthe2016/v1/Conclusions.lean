/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `Buthe2016.v1`

Büthe, *Estimating `π(x)` and related functions under partial RH assumptions*,
Math. Comp. **85** (2016), 2483–2498.

**Not `Buthe.v1`**, which is the same author's *An analytic method for bounding `ψ(x)`*,
Math. Comp. **87** (2018). `BKLNW` cites them as `[3]` and `[4]` respectively and uses both, which
is exactly the situation where matching a citation by author and topic goes wrong.

## What the paper gives the network

A conditional, and an unusually clean one. Schoenfeld proved his explicit bounds for `ψ`, `θ`, `π*`
and `π` *on the Riemann hypothesis*; this paper shows they already hold from a **partial**
verification, as long as `x` is small enough relative to the height reached — precisely
`4.92 √(x / log x) ≤ T`.

That makes it the bridge between the network's computational nodes and its analytic ones. A
verification node supplies `RiemannHypothesisUpTo T`; this supplies what may be concluded from it
below the corresponding `x`. `BKLNW` uses it as one of the three inputs to the `ε(b)` of its
Table 8, and `Platt–Trudgian`'s error-term paper cites it for the same purpose.

The conclusions below are stated as the paper states them: universally quantified in `T`, with the
verification as a hypothesis rather than an import. So this node imports nothing, and that is a
genuine `none` rather than an untraced `undetermined`.

## Watch the logarithmic integral

`li` here is the **un-offset** logarithmic integral, `∫₀ˣ dt / log t` in the principal-value sense,
which is what the paper writes and what Schoenfeld's bounds are stated against. It differs from
`Li` by `li 2 ≈ 1.045`, far from negligible at `√x log x / (8π)` precision. `FKS2` works with `Li`,
so a node combining the two must do the conversion rather than assume it away.
-/

namespace Buthe2016.v1

open IEANTN

/-- The paper's range condition: `4.92 √(x / log x) ≤ T`.

Node-local because it is this paper's own bookkeeping and nothing else has wanted it. Read it as
"the verification reached far enough for `x` to be covered". -/
noncomputable def withinRange (T x : ℝ) : Prop :=
  4.92 * Real.sqrt (x / Real.log x) ≤ T

/-- **Theorem 2, the `ψ` estimate.** If the Riemann hypothesis holds up to height `T`, then
`|ψ(x) − x| ≤ √x (log x)² / (8π)` for every `x > 59` within range.

This is Schoenfeld's bound, obtained from a partial verification rather than from the full Riemann
hypothesis. -/
def theorem_2_psi : Prop :=
  ∀ T : ℝ, RiemannHypothesisUpTo T → ∀ x : ℝ, 59 < x → withinRange T x →
    |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x) ^ (2 : ℕ) / (8 * Real.pi)

/-- **Theorem 2, the `θ` estimate.** `|θ(x) − x| ≤ √x (log x)² / (8π)` for every `x > 599` within
range, under a verification to height `T`.

Note the threshold is `599`, not the `59` of the `ψ` estimate. -/
def theorem_2_theta : Prop :=
  ∀ T : ℝ, RiemannHypothesisUpTo T → ∀ x : ℝ, 599 < x → withinRange T x →
    |Chebyshev.theta x - x| ≤ Real.sqrt x * (Real.log x) ^ (2 : ℕ) / (8 * Real.pi)

/-- **Theorem 2, equation (7.1).** `|π*(x) − li(x)| ≤ √x log x / (8π)` for every `x > 59` within
range, under a verification to height `T`.

`π*` is the Riemann prime-counting function `∑_{k ≥ 1} π(x^{1/k}) / k`, not `π`. The two differ by
roughly `√x / log x`, which is the size of this bound, so reading it as a statement about `π` would
be vacuous rather than merely imprecise — (7.2) below is the statement about `π`. -/
def theorem_2_li_minus_riemann_pi : Prop :=
  ∀ T : ℝ, RiemannHypothesisUpTo T → ∀ x : ℝ, 59 < x → withinRange T x →
    |riemannPrimeCounting x - li x| ≤ Real.sqrt x * Real.log x / (8 * Real.pi)

/-- **Theorem 2, equation (7.2).** `|π(x) − li(x)| ≤ √x log x / (8π)` for every `x > 2657` within
range, under a verification to height `T`.

The paper's headline: Schoenfeld's `π` bound, which he proved on the Riemann hypothesis, holding
from a partial verification. Note the threshold `2657` and that the comparison is against `li`, not
`Li`. -/
def theorem_2_li_minus_pi : Prop :=
  ∀ T : ℝ, RiemannHypothesisUpTo T → ∀ x : ℝ, 2657 < x → withinRange T x →
    |primeCounting x - li x| ≤ Real.sqrt x * Real.log x / (8 * Real.pi)

end Buthe2016.v1
