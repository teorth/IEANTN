/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.PrimeCounting

/-!
# Node `Buthe.v2`

The analytic transfer underlying Jan Büthe, *An analytic method for bounding `ψ(x)`*,
Math. Comp. **87** (2018), 1991–2009: his **Lemma 3**, which carries a two-sided bound on
`x − θ(x)` to one on `li(x) − π(x)`.

**A variant of `Buthe.v1`, not a successor.** `Buthe.v1` states the paper's Theorem 2 — the six
numerical estimates on `[1, 10¹⁹]` that the network consumes. This node states the machinery those
estimates are obtained *with*, for arbitrary parameters rather than at Büthe's. Both stay; see
`docs/NODES.md` on versions as variants.

## Why this node exists

Two of Theorem 2's six equations are **derived** rather than computed, and the paper says so. From
its proof:

* "Choosing `a = 1,500` in Lemma 3 and using (1.6) gives **(1.9)** for `10⁷ ≤ x ≤ 10¹⁹` and the
  remaining values have again been checked directly."
* "The bound **(1.10)** follows from (1.7) and [14, Theorem 19]."

Lemma 3 has two parts, and each is the vehicle for one of them: the two-sided estimate below gives
(1.9) from (1.6), and the positivity clause gives (1.10) from (1.7). So this one node unlocks both.

Both conclusions **import nothing**. Every input arrives as a hypothesis, so a Lean proof is their
whole justification and they can be verified without waiting on any numerical input — the same
shape as `FKS2.v2`'s pipelines, and the reason this node is separable from `Buthe.v1` at all.

## What a proof will rest on

The paper proves both parts from the partial-summation identity it labels (6.17),

`π(x) − π(a) = li(x) − li(a) − (x − θ(x))/log x + (a − θ(a))/log a − ∫ₐˣ (t − θ(t))/(t log²t) dt`,

which is the same species of argument as `Solutions/FKS2.v2/Stieltjes.lean`.

Neither part is self-contained numerically. The two-sided estimate carries the constant `A` below
through to its conclusion, and Büthe's use of it at `a = 1500` needs `A ≤ 0` there; the positivity
clause is proved by taking `a = 10` in (6.17), using `π(10) − li(10) + (10 − θ(10))/log 10 > 0.1`.
Both of those are finite checks and live on `ButheNumerics.v1`.

## Conventions

`li` is the **un-offset** logarithmic integral and `π` the ordinary prime-counting function, both
matching `Buthe.v1`. `li 2 ≈ 1.045`, so a consumer working with `Li` must convert rather than
assume the difference away.
-/

namespace Buthe.v2

open IEANTN

/-- The constant Büthe's Lemma 3 carries through, at a left endpoint `a`:
`A(a) = π(a) − li(a) + (a − θ(a)) / log a`.

Node-local: it is this lemma's own bookkeeping and nothing else has wanted it. Spelled the same way
in `ButheNumerics.v1`, where its sign at the two points Büthe uses is asserted. -/
noncomputable def lemma3A (a : ℝ) : ℝ :=
  primeCounting a - li a + (a - Chebyshev.theta a) / Real.log a

/-- **Lemma 3, the two-sided estimate.**

If `c ≤ (x − θ(x))/√x ≤ C` for every `x ∈ [a, b]`, with `b > 10⁷`, `12 < a < b`, `c ≤ 0 ≤ C`, then
for every `x ∈ [max(a, 10⁷), b]`,

`(li(x) − π(x)) / (√x / log x) ≤ (x − θ(x))/√x + (2C / log x)(1 + 5 / log x) + A(a) log x / √x`

and the matching lower bound with `c` in place of `C`.

This is what turns a `θ` estimate into a `π` one. Büthe applies it at `a = 1500` with `C = 1.95`
from his (1.6): multiplying through by `√x / log x` sends the last term to the constant `A(a)`, and
the middle term becomes `3.9 / log x + 19.5 / (log x)²` — note `3.9 = 2C` and `19.5 = 10C`, which
are exactly the constants printed in (1.9). Since (1.9) as printed carries **no** additive
constant, it is this lemma together with `A(1500) ≤ 0`, which the paper does not display and
`ButheNumerics.v1.lemma_3_constant_nonpos` states.

The lower endpoint `max(a, 10⁷)` is the lemma's own, not a convenience: below `10⁷` the estimate is
not claimed, which is why Büthe checks that range directly. -/
noncomputable def lemma_3_bounds : Prop :=
  ∀ a b c C : ℝ, (10 : ℝ) ^ (7 : ℕ) < b → 12 < a → a < b → c ≤ 0 → 0 ≤ C →
    (∀ x ∈ Set.Icc a b,
      c ≤ (x - Chebyshev.theta x) / Real.sqrt x ∧
        (x - Chebyshev.theta x) / Real.sqrt x ≤ C) →
    ∀ x ∈ Set.Icc (max a ((10 : ℝ) ^ (7 : ℕ))) b,
      (li x - primeCounting x) / (Real.sqrt x / Real.log x) ≤
          (x - Chebyshev.theta x) / Real.sqrt x
            + 2 * C / Real.log x * (1 + 5 / Real.log x)
            + lemma3A a * Real.log x / Real.sqrt x ∧
        (x - Chebyshev.theta x) / Real.sqrt x
            + 2 * c / Real.log x * (1 + 5 / Real.log x)
            + lemma3A a * Real.log x / Real.sqrt x
          ≤ (li x - primeCounting x) / (Real.sqrt x / Real.log x)

/-- **Lemma 3, the positivity clause.** For every `T`, if `t − θ(t) > 0` throughout `[2, T]` then
`li(t) − π(t) > 0` throughout `[2, T]`.

Stated by Büthe as "Furthermore, the implication … holds", and it is the vehicle for Theorem 2's
(1.10): his (1.7) gives `x − θ(x) > 0.05√x > 0` on `[1, 10¹⁹]`, and this converts that into
`li(x) − π(x) > 0` on the same range — which is the new lower bound for the Skewes number that the
paper advertises.

The proof of Theorem 2 attributes (1.10) to "(1.7) and [14, Theorem 19]", where [14] is
Rosser–Schoenfeld's *Approximate formulas for some functions of prime numbers*, Illinois J. Math.
**6** (1962) — **not** the Rosser–Schoenfeld paper this network holds, which is *Sharper bounds*,
Math. Comp. **29** (1975). Whether that citation is an alternative route or supplies a step inside
this clause has not been determined here; what is certain is that this clause has exactly the shape
(1.7) ⟹ (1.10) needs.

Büthe's own proof of it takes `a = 10` in his identity (6.17), using
`π(10) − li(10) + (10 − θ(10))/log 10 > 0.1` — that is `lemma3A 10 > 0.1`, a finite check stated on
`ButheNumerics.v1`. So a solution proving this conclusion will need that as a hypothesis or will
have to establish it. -/
def lemma_3_positivity : Prop :=
  ∀ T : ℝ, (∀ t : ℝ, 2 ≤ t → t ≤ T → 0 < t - Chebyshev.theta t) →
    ∀ t : ℝ, 2 ≤ t → t ≤ T → 0 < li t - primeCounting t

end Buthe.v2
