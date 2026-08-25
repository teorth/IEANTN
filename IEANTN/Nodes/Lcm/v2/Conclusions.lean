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

If some `c ≥ 5` bounds `log X₀` from below, and every `x ≥ X₀` admits a prime in
`(x, x + x/(log x)³]`, then `Lₙ = lcm(1, …, n)` fails to be highly abundant for every `n ≥ X₀²`.

## What `c` is, and where the bound on it comes from

`c` is a lower bound for `log √n`, and the *only* thing the argument uses it for: it bounds the
relative gap `ε = 1/(log √n)³ ≤ 1/c³`. The argument adjoins three primes just above `√n` and
removes three just below `n`, and closes exactly when the resulting comparison of products holds,
which is a numerical condition on `ε` and on `X₀`.

An earlier version of this statement wrote `11.4` here instead. That number is not a property of
the argument at all — it is `log 89693` rounded down, which is to say it came from the threshold
`Lcm.v1` happens to use. Reading the constraint out of the development
(`Solutions/Lcm.v1/LcmDev.lean`) and evaluating it gives a genuine threshold near **`c > 4.12`**,
attained in the worst permitted case `X₀ = eᶜ`; at `X₀ = 89693` it is nearer `3.6`. `5` is that
threshold with margin, chosen so a solver has room and so the constant is not itself a fitted
number. **The margin is deliberate and the bound is not claimed to be sharp.**

## `c` is eliminable, and is kept anyway

Since the conclusion does not mention `c`, this is equivalent to `5 ≤ log X₀ → …`. The parameter
earns its place as documentation rather than logic: it names the quantity the numerics constrain,
so a sharper analysis lowers a stated bound instead of silently changing a magic number, and a
reader can see that `11.4` was never doing the work it appeared to be doing.

The practical gain is the lowered bound, not the parameter: a prime-gap result at any threshold
above `e⁵ ≈ 149` now feeds this node, where `11.4` demanded one above `89000`. -/
def lcmUpto_not_highlyAbundant_of_primeGap : Prop :=
  ∀ c X₀ : ℝ, 5 ≤ c → c ≤ Real.log X₀ → IEANTN.HasPrimeInInterval.logPower X₀ 3 →
    ∀ n : ℕ, X₀ ^ 2 ≤ (n : ℝ) → ¬ HighlyAbundant (Nat.lcmUpto n)

end Lcm.v2
