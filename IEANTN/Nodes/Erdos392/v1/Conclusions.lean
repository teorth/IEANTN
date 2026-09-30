/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Node `Erdos392.v1` — how few factors of size at most `n²` multiply to `n!`

Erdős problem 392. Write `A(n)` for the least `t` such that `n! = a₁⋯aₜ` with every `aᵢ ≤ n²`.
The problem asks whether

`A(n) = n/2 − n/(2 log n) + o(n/log n)`,

and it does. The two halves are `factors_le_n_sq` and `factors_le_n_sq_lower` below, and they are
of very different character: the upper bound is the whole content, and the lower bound is a line of
counting.

`factors_le_n` is the intermediate result the upper bound is built on — the same question with
factors of size at most `n` rather than `n²`, where the answer is `n − n/log n + o(n/log n)`.
Pairing those factors is what halves the count.

## This node imports nothing

Which is worth saying, because the development it comes from does not look unconditional.
PrimeNumberTheoremAnd's proof uses the Prime Number Theorem, `π(x) ~ x/log x`, at two points. Both
are upper bounds on `π`, and its own blueprint note says as much: *"use the prime number theorem
(or the Chebyshev bound)"*. Mathlib's `Chebyshev.eventually_primeCounting_le` is that Chebyshev
bound, and at `ε = 1/10` it gives `π(x) ≤ 1.487 x/log x` — sharper than the `1.5 x/log x` the two
proofs actually consume. So the solution uses it and the whole chain from Mathlib to here is proof
rather than citation.

## On the shape of the statements

Both upper bounds are stated as "for every `ε > 0`, eventually in `n`", which is what
`o(n/log n)` means and what the proof produces. The factorisation is given as a function
`Fin t → ℕ` rather than as a multiset or a list, so that `t` is visible as the thing being bounded.

The cardinality bound sits **outside** the quantifier over the factors, unlike in PNT+, where it is
written inside: `∀ i, aᵢ ≤ n² ∧ t ≤ B`. That form is equivalent to this one only because the
product condition forces `t > 0` — with an empty index type it would hold vacuously with no bound
at all. The two are the same claim here and the shape below is the one that does not need the
argument.
-/

namespace Erdos392.v1

open Filter Nat

/-- **Factors of size at most `n`.** For every `ε > 0`, eventually `n!` is a product of at most
`n − n/log n + ε n/log n` positive integers, each at most `n`.

The intermediate bound, and where the work is: the factorisation is built by starting from the
multiset of `n/p` for primes `p ≤ n` and repairing it, the count being controlled by a "score"
that the repair steps do not increase. -/
def factors_le_n : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ (t : ℕ) (a : Fin t → ℕ), (∏ i, a i = n !) ∧ (∀ i, a i ≤ n) ∧
      (t : ℝ) ≤ n - n / Real.log n + ε * n / Real.log n

/-- **Erdős 392, the upper bound.** For every `ε > 0`, eventually `n!` is a product of at most
`n/2 − n/(2 log n) + ε n/log n` positive integers, each at most `n²`.

Obtained from `factors_le_n` by pairing: two factors of size at most `n` multiply to one of size at
most `n²`, so the count halves, and the pairing can be arranged to leave nothing over. -/
def factors_le_n_sq : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ (t : ℕ) (a : Fin t → ℕ), (∏ i, a i = n !) ∧ (∀ i, a i ≤ n ^ 2) ∧
      (t : ℝ) ≤ n / 2 - n / (2 * Real.log n) + ε * n / Real.log n

/-- **Erdős 392, the lower bound.** For every `n ≥ 2`, *any* way of writing `n!` as a product of
integers each at most `n²` uses at least `n/2 − n/(2 log n)` of them.

The easy half, and stated in the strongest form it takes: no `ε`, no "eventually", every `n ≥ 2`.
If `n! = a₁⋯aₜ` with each `aᵢ ≤ n²` then `n! ≤ (n²)ᵗ`, so `t ≥ log n!/(2 log n)`, and Stirling's
bound `log n! ≥ n log n − n + (log n)/2 + log(2π)/2` — which Mathlib has effectively, for every
`n ≠ 0` — gives the claim with room to spare.

Together with `factors_le_n_sq` this is the asymptotic the problem asks for, since the gap between
the two bounds is `ε n/log n` for every `ε > 0`. -/
def factors_le_n_sq_lower : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (t : ℕ) (a : Fin t → ℕ), (∏ i, a i = n !) → (∀ i, a i ≤ n ^ 2) →
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ t

end Erdos392.v1
