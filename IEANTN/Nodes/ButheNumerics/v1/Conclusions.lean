/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.Numerics

/-!
# Node `ButheNumerics.v1`

The finite numerical checks inside Jan Büthe, *An analytic method for bounding `ψ(x)`*,
Math. Comp. **87** (2018), 1991–2009, separated from the analysis that consumes them.

Same paper as `Buthe.v1`, different kind of claim — a computation someone ran, rather than an
argument a referee followed. Keeping the two apart lets a consumer see which half of its trust is
which, as `FKS2Numerics.v1` does for `FKS2`.

## What is here and what is not

`Buthe.v1` states the paper's **Theorem 2**, equations (1.5) through (1.10). Those stay there: they
are the paper's displayed results and what the network consumes. This node holds the *auxiliary*
finite checks that Theorem 2's own proof uses and that the paper does not display.

The distinction matters because two of Theorem 2's six equations are **derived** rather than
computed, and the paper says so. Reading its proof:

* (1.5) is the method's output for `ψ`, with `11 < t < 100` "easily checked";
* (1.6) and (1.7) come from the paper's Lemma 1 with `a = 100`, `b = 5·10¹⁰`, `C = 0.81`, covering
  `10⁷ ≤ x ≤ 5·10¹⁰`, with the rest computed;
* (1.8) comes "similarly" from the bounds of the paper's Table 2, for `x ≥ 10⁷`;
* **(1.9) follows from (1.6)** by the paper's Lemma 3 at `a = 1500`, for `10⁷ ≤ x ≤ 10¹⁹`, "and the
  remaining values have again been checked directly";
* **(1.10) follows from (1.7)** and Rosser–Schoenfeld 1962, Theorem 19.

So (1.9) and (1.10) are the two places where a Lean proof could replace an assertion, given the
right inputs. The two conclusions below are exactly the inputs Lemma 3 needs that are *not*
already stated somewhere in the network.

## Why `A ≤ 0` is the interesting one

Büthe's Lemma 3 concludes, for `c ≤ (x − θ(x))/√x ≤ C` on `[a, b]` and
`A = π(a) − li(a) + (a − θ(a)) / log a`,

`(li x − π x) / (√x / log x) ≤ (x − θ x)/√x + (2C / log x)(1 + 5 / log x) + A · log x / √x`.

Multiplying through by `√x / log x` turns the last term into the constant `A`. With `C = 1.95`
from (1.6), the first three terms are exactly (1.9)'s
`1.95 + 3.9 / log x + 19.5 / (log x)²` — note `3.9 = 2C` and `19.5 = 10C`, which is the tell that
(1.9) is (1.6) pushed through Lemma 3. **So (1.9) as printed holds only if `A ≤ 0`**, and the paper
does not display that check. It is stated below.

These are `li`, the **un-offset** logarithmic integral, and `π`, the ordinary prime-counting
function — matching `Buthe.v1`. `li 2 ≈ 1.045`, so a consumer working with `Li` must convert.
-/

namespace ButheNumerics.v1

open IEANTN

/-- **The constant in Büthe's Lemma 3 at `a = 1500` is non-positive.**

`A = π(1500) − li(1500) + (1500 − θ(1500)) / log 1500 ≤ 0`.

The hidden hypothesis of Theorem 2's equation (1.9). Lemma 3 carries `A` through as an additive
constant on the right, so (1.9) as printed — which has no such term — is the specialisation at
`a = 1500` *together with* the fact that this `A` is not positive. The paper chooses `a = 1500` and
does not display the evaluation.

A finite check: three evaluations at a single point. Nothing in the network proves it, and it is
asserted on the paper's authority, but it is the sort of thing a Lean proof could discharge
outright, unlike the bounds on `[2, 10¹⁹]` above it.

**No `margin` site here, deliberately.** The bound is `0`, and `margin n * 0 = 0` for every `n`,
so a multiplicative margin cannot loosen this claim at all — a site here would look like slack that
does not exist. If roundoff ever turns out to matter for this evaluation, the honest repair is a
new version stating an explicit positive bound, not a margin index. -/
noncomputable def lemma_3_constant_nonpos : Prop :=
  primeCounting 1500 - li 1500 + (1500 - Chebyshev.theta 1500) / Real.log 1500 ≤ 0

/-- **Theorem 2's equation (1.9), on the range the paper checks directly.**

`li(x) − π(x) ≤ (√x / log x) (1.95 + 3.9 / log x + 19.5 / (log x)²)` for `2 ≤ x ≤ 10⁷`.

Lemma 3 gives (1.9) only for `10⁷ ≤ x ≤ 10¹⁹`; below `10⁷` the paper says "the remaining values
have again been checked directly". That direct check is a separate claim from the analysis, and
this is it.

Stating it means `Buthe.v1.theorem_2_li_minus_pi` becomes a claim with all of its inputs written
down: this conclusion on `[2, 10⁷]`, and Lemma 3 applied to (1.6) above it.

Carries a `margin 0` factor — see `IEANTN.margin`. -/
noncomputable def li_minus_pi_below_1e7 : Prop :=
  ∀ x : ℝ, 2 ≤ x → x ≤ 10 ^ (7 : ℕ) →
    li x - primeCounting x ≤
      margin 0 * (Real.sqrt x / Real.log x *
        (1.95 + 3.9 / Real.log x + 19.5 / (Real.log x) ^ (2 : ℕ)))

/-- **The constant in Büthe's Lemma 3 at `a = 10` exceeds `0.1`.**

`π(10) − li(10) + (10 − θ(10)) / log 10 > 0.1`.

The second hidden numerical input, and the one behind Theorem 2's equation (1.10). Büthe proves the
positivity clause of Lemma 3 — that `t − θ(t) > 0` throughout `[2, T]` forces `li(t) − π(t) > 0`
there — by "taking `a = 10` in (6.17) since `π(10) − li(10) + (10 − θ(10))/log 10 > 0.1`". That
inequality is displayed in the proof but is not a stated result, and nothing else in the network
carries it.

Note the sign differs from `lemma_3_constant_nonpos`: the same functional `A(a)` is asserted
positive at `a = 10` and non-positive at `a = 1500`. That is not a contradiction — `A` varies with
`a` — but it is worth seeing side by side, because a solution that conflates the two points will
prove nothing.

A finite check: three evaluations at a single point. No `margin` site — the bound `0.1` is a
strict lower bound on a quantity, and a multiplicative margin loosens an upper bound, so a site
here would point the wrong way. -/
noncomputable def lemma_3_constant_gt_at_10 : Prop :=
  0.1 < primeCounting 10 - li 10 + (10 - Chebyshev.theta 10) / Real.log 10

end ButheNumerics.v1
