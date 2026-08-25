/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import IEANTN.Vocabulary.PrimeGaps

/-!
# Node `Lcm.v2` — the abstract form

`Lcm.v1` records the result as its source states it: `Lₙ` is not highly abundant for `n ≥ 89693²`,
given Dusart's Proposition 5.4. That threshold is an artefact of the prime-gap result it happens to
use, not of the argument.

This version states what the argument actually shows: **any** prime-gap result of Dusart's shape,
at any threshold large enough for the estimates to close, gives the same conclusion above the square
of that threshold. `Lcm.v1` is then the instance at `89693`.

The two coexist deliberately. `v1` is the version to cite against the literature, and the one that
carries a direct Comparator receipt; `v2` is the one another node can reuse when a sharper prime-gap
input becomes available. Neither obsoletes the other, and nothing here deprecates `v1`.

**This node has no imports.** The Dusart-type hypothesis is *internal* to the statement rather than
an edge in the graph, which is what makes the node reusable: a downstream user supplies whichever
prime-gap result they have, instead of inheriting the one `v1` happens to depend on.
-/

namespace Lcm.v2

open ArithmeticFunction

/-- A positive integer `N` is **highly abundant** if `σ(N) > σ(m)` for every `m < N`.

Deliberately restated here rather than imported from `Lcm.v1`: a conclusions file may import
another node's conclusions, but doing so for a *definition* would make this node's statement depend
on `v1` existing, when the point of `v2` is to stand alone. If a third node needs abundance, this
moves to Vocabulary. -/
def HighlyAbundant (N : ℕ) : Prop := ∀ m : ℕ, m < N → sigma 1 m < sigma 1 N

/-- **The argument, with its threshold abstracted.**

If `X₀` is large enough that `log X₀ > 11.4`, and every `x ≥ X₀` admits a prime in
`(x, x + x/(log x)³]`, then `Lₙ = lcm(1, …, n)` fails to be highly abundant for every `n ≥ X₀²`.

The side condition is exactly what the estimates need: the argument compares products of three
primes just above `√n` against three just below `n`, and the comparison closes once
`ε = 1/(log √n)³` is small enough, which `log √n ≥ 11.4` secures.

`11.4` is not sacred — it is the bound the existing proof happens to use, and a sharper analysis
would lower it. What matters is that the threshold and the prime-gap input move together, which is
what `v1` cannot express. -/
def lcmUpto_not_highlyAbundant_of_primeGap : Prop :=
  ∀ X₀ : ℝ, 11.4 < Real.log X₀ → IEANTN.HasPrimeInInterval.logPower X₀ 3 →
    ∀ n : ℕ, X₀ ^ 2 ≤ (n : ℝ) → ¬ HighlyAbundant (Nat.lcmUpto n)

end Lcm.v2
