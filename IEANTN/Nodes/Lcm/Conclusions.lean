/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Node `Lcm` — the least common multiple sequence is not highly abundant for large `n`

Refutation of a conjecture of José Damián Espinosa, raised on MathOverflow in October 2025: that
every term of `Lₙ = lcm(1, 2, …, n)` is a highly abundant number.

The conjecture is false, and false in a strong sense — `Lₙ` fails to be highly abundant for *every*
`n ≥ 89693²`, not merely infinitely often.

Alaoglu and Erdős (1944, pp. 466–467) had already asserted that neither `n!` nor `lcm(1, …, n)` can
be highly abundant infinitely often, but gave no proof. That assertion is weaker than the statement
proved here, and this node does not depend on it.
-/

namespace Lcm

open ArithmeticFunction

/-- A positive integer `N` is **highly abundant** if `σ(N) > σ(m)` for every `m < N`, where `σ` is
the sum-of-divisors function.

Node-local for now. If a second node needs abundance notions this moves to Vocabulary unchanged. -/
def HighlyAbundant (N : ℕ) : Prop := ∀ m : ℕ, m < N → sigma 1 m < sigma 1 N

/-- **`Lₙ` is not highly abundant for `n ≥ 89693²`.**

`Nat.lcmUpto n` is `lcm(1, 2, …, n)`. The threshold `89693²` is inherited from the threshold
in Dusart's Proposition 5.4, which supplies the primes the argument needs; it is an artefact of that
input rather than of the method, and would improve if a sharper prime-gap result were imported.

The argument, due to Terence Tao: adjoin three primes slightly above `√n` to `Lₙ` and remove three
primes slightly below `n`, chosen so the product removed slightly exceeds the product adjoined. The
result is a smaller integer with a larger sum of divisors, contradicting high abundance. -/
def lcmUpto_not_highlyAbundant : Prop :=
  ∀ n : ℕ, 89693 ^ 2 ≤ n → ¬ HighlyAbundant (Nat.lcmUpto n)

end Lcm
