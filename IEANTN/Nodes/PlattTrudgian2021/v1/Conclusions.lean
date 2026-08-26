/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.PlattTrudgian2021.v1.Tables

/-!
# Node `PlattTrudgian2021.v1`

Platt and Trudgian, *The error term in the prime number theorem*,
Math. Comp. **90** (2021), no. 328, 871–881.

**Not `PlattTrudgian.v1`**, which is the same two authors' *The Riemann hypothesis is true up to
`3 · 10¹²`*. `BKLNW` cites them as `[37]` and `[38]`, and uses both for different things — this one
for its `ψ` bounds, the other for the verification height they rest on. Two papers, two adjacent
reference numbers, same authors: the case where matching a citation by author goes wrong.

## What the network takes from it

Its Theorem 1 is where `BKLNW`'s Table 8 gets its large-`b` half: `BKLNW` says it uses
"[3, Theorem 2], [4, Theorem 1] and [37, Theorem 1]" to compute the `ε(b)` it needs, and that
"Platt and Trudgian use a truncated Perron's formula combined with the zero density obtained in
[25]", which is `KLN`. Their technique wins for `x` beyond about `e²³⁰⁰`; Büthe's wins below it.

The paper also makes explicit a theorem of Pintz and applies it to a Ramanujan inequality; that
part (its Theorem 2) is not stated here because nothing in the network consumes it.

## The zero-free region it uses

`R = 5.573412` — which is exactly `MT.v1.zero_free_region`, the *unsharpened* Theorem 1 value, not
the `5.5666305` of `MT`'s §6.1 that the `FKS` chain runs on. That is a real import edge, and it is
worth noticing that two different constants from the same paper feed two different parts of the
network.
-/

namespace PlattTrudgian2021.v1

open IEANTN

/-- **Theorem 1, the asymptotic bound.** For each row `(X, A, B, C, ε₀)` of Table 1,
`Eψ` obeys the classical admissible bound with `A`, `B`, `C` and `R = 5.573412` for all
`x ≥ e^X`.

Note on absolute values, as for `FKS` and `FKS2`. The paper writes this as
`(ψ(x) − x)/x ≤ A (log x / R)^B exp(−C √(log x / R))`, on a signed quantity and with no bars, while
`Eψ` here is `|ψ(x) − x| / x`. So against the printed line alone this is the stronger claim. Unlike
`FKS`, this paper gives no two-sided restatement of *this* bound in its abstract — what it does
give two-sided is the `ε₀` column, stated as `|ψ(x) − x| ≤ ε₀ x` in the same theorem, which is
`theorem_1_numerical` below. Prefer that one where it suffices. -/
def theorem_1_classical : Prop :=
  ∀ X A B C ε : ℝ, (X, A, B, C, ε) ∈ table1 →
    HasClassicalBound Eψ A B C 5.573412 (Real.exp X)

/-- **Theorem 1, the numerical bound.** For each row `(X, A, B, C, ε₀)` of Table 1,
`|ψ(x) − x| ≤ ε₀ x` for all `x ≥ e^X`.

This half of Theorem 1 is printed with explicit absolute value bars, so it needs none of the
caveat above. It is also the half `FKS` compares itself against: its abstract quotes the `X = 3000`
row's `4.51 · 10⁻¹³` as the figure it improves to `4.9678 · 10⁻¹⁵`. -/
def theorem_1_numerical : Prop :=
  ∀ X A B C ε : ℝ, (X, A, B, C, ε) ∈ table1 →
    HasNumericalBound Eψ ε (Real.exp X)

end PlattTrudgian2021.v1
