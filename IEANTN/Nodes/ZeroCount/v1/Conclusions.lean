/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `ZeroCount.v1`

Rosser's explicit bound on the Riemann–von Mangoldt error term, as Chirre–Helfgott restate it in
Lemma B.1 of arXiv:2512.15709 and use throughout their Appendix B.

Writing `N(t)` for the number of zeroes of `ζ` with `0 < Im ρ ≤ t`, counted with multiplicity, and

`Q(t) = N(t) - ((t/2π) log(t/2π) - t/2π + 7/8)`,

the claims are `|Q(t)| < 1` for `0 < t ≤ 280` and `|Q(t)| ≤ (1/5) log t + 2` for `t ≥ 1`.

Split out as its own node rather than stated inside `CH2` because it is not Chirre–Helfgott's
result — they cite Rosser 1941 for it, remarking that "one can prove better bounds nowadays; we use
an older result here to minimize dependencies" — and because a zero count is exactly the kind of
input several papers want. It is the missing input for `C_T = (1/2π)log²(T/2π) - (1/6π)log(T/2π)`,
the constant in `CH2.v1`'s corollaries, which comes from summing over zeroes against `N`.

## Why this does **not** use `IEANTN.HasRvMBound`

That would have been the obvious composable choice — `HasRvMBound b₁ b₂ b₃` is literally
`|Q(T)| ≤ b₁ log T + b₂ log log T + b₃`, and this is `b₁ = 1/5`, `b₂ = 0`, `b₃ = 2`. It is the wrong
statement here, and the reason is a counting convention, not a constant.

`HasRvMBound` is built on `zetaN`, which counts `Set.Ioo 0 T` — zeroes with `0 < Im ρ < T`. Rosser
and Chirre–Helfgott count `0 < Im ρ ≤ T`. So the conclusions below use the source's convention,
written out from `zetaZeroesSum` with `Set.Ioc`, and need no new definition for it.

The two conventions differ by `m(t)`, the multiplicity at height exactly `t`, and comparing them at a
single height makes them look inequivalent — the upper bound transfers, the lower one loses `m(t)`.
**That comparison is the wrong one.** The hypothesis holds at every nearby height, and the zeroes in
a bounded region are finite, so there is an `s < t` with `N_Ioc(s) = N_Ioo(t)` exactly; substituting
and letting `s ↑ t`, with the main term and the bound both continuous, gives the open-interval form
with **no loss of constant**.

So the two are equivalent, and stating the source's convention here costs a consumer only a lemma
nobody has yet written. The clean shape for that is the `ZeroFreeHeight` pattern — keep both
conventions and let a node or bridge record the passage between them — rather than forcing one
convention on Vocabulary.

## A note on the sum

`zetaZeroesSum` carries a junk-value warning — `tsum` of a non-summable family is `0`. It does not
bite here: the zeroes of `ζ` in a bounded rectangle are finite in number, so the family has finite
support and the sum is the honest count. That is a *fact* about `ζ` rather than a hypothesis, which
is why no summability condition appears below; a reader checking these statements should confirm it
rather than take it on trust.
-/

namespace ZeroCount.v1

open Real IEANTN

/-- `N(t)`, the number of zeroes of `ζ` with `0 < Im ρ ≤ t`, counted with multiplicity.

Note `Set.Ioc`, matching Rosser and Chirre–Helfgott. `IEANTN.zetaN` uses `Set.Ioo`; see the module
docstring for why the difference is not cosmetic. Node-local, and deliberately so — promoting it
would put two nearly identical counts in Vocabulary, which is worse than the asymmetry it fixes. -/
noncomputable def zetaNClosed (t : ℝ) : ℝ :=
  zetaZeroesSum Set.univ (Set.Ioc 0 t) fun _ ↦ 1

/-- The Riemann–von Mangoldt main term, `(t/2π) log(t/2π) - t/2π + 7/8`.

Written out rather than reused from `IEANTN.HasRvMBound` so that the two are visibly the same
expression and only the counting range differs. -/
noncomputable def rvmMain (t : ℝ) : ℝ :=
  t / (2 * π) * log (t / (2 * π)) - t / (2 * π) + 7 / 8

/-- **Lemma B.1, second half.** `|Q(t)| ≤ (1/5) log t + 2` for `t ≥ 1`.

Chirre–Helfgott derive this from Rosser's `|Q(t)| ≤ 0.137 log t + 0.443 log log t + 1.588` for
`t ≥ 2`, checking that `0.137 log t + 0.443 log log t + 1.588 < (1/5) log t + 2` for `t ≥ 5400` and
computing directly below that. So the constants here are theirs, not Rosser's, and are weaker than
what is available — deliberately, to keep the dependency to one 1941 paper.

Imports nothing: this is a fact about `ζ` with no network input. -/
def rvm_error_bound : Prop :=
  ∀ t : ℝ, 1 ≤ t → |zetaNClosed t - rvmMain t| ≤ (1 / 5) * log t + 2

/-- **Lemma B.1, first half.** `|Q(t)| < 1` for `0 < t ≤ 280`.

Strict, and stated separately because it is a different claim rather than a special case: on this
range `(1/5) log t + 2` exceeds `2`, so the general bound is far weaker than the truth. Chirre and
Helfgott use both halves, the small-range one where the general bound would be too lossy.

Imports nothing. -/
def rvm_error_small : Prop :=
  ∀ t : ℝ, 0 < t → t ≤ 280 → |zetaNClosed t - rvmMain t| < 1

end ZeroCount.v1
