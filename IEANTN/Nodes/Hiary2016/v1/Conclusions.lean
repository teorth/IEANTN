/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `Hiary2016.v1`

Hiary, *An explicit van der Corput estimate for `ζ(1/2 + it)`*, Int. J. Number Theory (2016);
[arXiv:1507.01261](https://arxiv.org/abs/1507.01261).

The subconvexity bound on the critical line that `KLN` uses. `KLN`'s source says so exactly:
"Statement (3.2) is `[Hiary, Theorem 1.1]`".

## The constant is corrected, as on `KLN.v1`

Hiary's Theorem 1.1 prints `0.63`. That value depends on an explicit version of van der Corput's
second-derivative test due to Cheng and Graham which was later found to be erroneous; accounting
for the correction moves the constant to `0.77`. `FKS` states this plainly — "with `a₁ = 0.63`
relies on an erroneous explicit version of van der Corput second derivative test due to
Cheng–Graham. See [Patel, Footnote 3] for details. After accounting for this correction, the
constant `a₁` changes to `0.77`" — and its own tables are computed with `0.77`.

So `0.77` is stated here, for the reason `KLN.v1` states it: a node carrying a value known to be
wrong is worse than no node, and the correction restores the whole chain rather than breaking it.
The docstring is where the discrepancy with the printed paper lives.

`FKS` also notes that Hiary, Patel and Yang have since recovered and improved the constant to
`0.618` (`HiaryPatelYang` is held but has no node). That would sharpen everything downstream, and
is the obvious thing to revisit when the chain is re-run.

## What is not stated

Theorem 1.1 has a second half — `|ζ(1/2 + it)| ≤ 1.461` for `0 ≤ t ≤ 3` — which nothing in the
network consumes. Whether it is affected by the same correction has not been checked, which is
itself a reason not to state it here on the strength of a guess.
-/

namespace Hiary2016.v1

open IEANTN

/-- **Theorem 1.1, the `t ≥ 3` half, with the constant corrected.**
`|ζ(1/2 + it)| ≤ 0.77 · t^{1/6} · log t` for every `t ≥ 3`.

The paper prints `0.63`; see the module docstring for why `0.77` is stated. This is the statement
`KLN`'s Lemma 3.2 quotes and that the `FKS` chain ultimately consumes. -/
def zeta_half_line_bound : Prop :=
  ∀ t : ℝ, 3 ≤ t →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.77 * t ^ ((1 : ℝ) / 6) * Real.log t

end Hiary2016.v1
