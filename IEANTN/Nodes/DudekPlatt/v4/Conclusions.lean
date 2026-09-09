/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting

/-!
# Node `DudekPlatt.v4`

**Ramanujan's inequality above `exp(9401)`**, from Dudek and Platt's own **footnote 1** pairing
`a = 3130`, `R = 6.315` (Mossinghoff–Trudgian's improved zero-free region), run through the
**repaired** `DudekPlatt.v3.criterion` rather than the paper's own defective Lemma 2.1.

A **variant** of `DudekPlatt.v1` and `.v2`, not a successor — all four coexist:

* `DudekPlatt.v1` is the paper's own printed threshold, `exp(9658)`, on citation.
* `DudekPlatt.v2` is `PrimeNumberTheoremAnd`'s threshold, `exp(3915)`, far sharper but resting on
  an unverified Lean development's literal bounds.
* `DudekPlatt.v3` is the repaired pipeline itself, parameter-free.
* this node evaluates that pipeline at the paper's *own* footnote-improved parameters, giving
  `exp(9401)` — strictly stronger than `.v1` (`exp(9401) < exp(9658)`), unconditional, and not
  resting on any development outside this paper and Mossinghoff–Trudgian's.

## Why this is not simply `DudekPlatt.v1` with a smaller number

The paper's footnote 1 itself claims `exp(9394)` at these parameters — but through its own
*unrepaired* Lemma 2.1, the same defective argument `DudekPlatt.v3`'s docstring documents. The
repair costs real margin (documented on `DudekPlatt.v1`: `~1.93` at the paper's own `a = 3223`,
enough to move the paper's `exp(9658)` out of reach at that choice, requiring `exp(9659)`
instead). Re-running the footnote's own parameters through the *repaired* criterion is genuinely
new work, not a relabelling of the footnote's number, which is why `exp(9401)` — not `exp(9394)` —
is what this node states. See `DudekPlattNumerics.v3` for where `9401 = 9400 + 1` comes from.

This also answers issue #63 directly: the paper's own printed `exp(9658)` recovers under the
repaired criterion once the footnote's sharper `(a, R)` is used in place of the main text's, with
`257` log-units to spare — `exp(9401) < exp(9658)`, so this conclusion implies `DudekPlatt.v1`'s by
the same monotonicity argument that already relates `.v2` to `.v1`.
-/

namespace DudekPlatt.v4

open IEANTN

/-- **Ramanujan's inequality above `exp(9401)`.**

`π(x)² < (e x / log x) · π(x/e)` for every `x > exp(9401)`.

The same statement as `DudekPlatt.v1.ramanujan_inequality` at a much smaller threshold — this
conclusion is **strictly stronger** and implies it, `exp(9401) < exp(9658)`, exactly as
`DudekPlatt.v2`'s `exp(3915)` already does. Strict `<`, matching `.v2`'s convention and
`DudekPlatt.v3.criterion`'s own conclusion shape, rather than `.v1`'s non-strict `≥` on the paper's
own printed threshold. -/
noncomputable def ramanujan_inequality_9401 : Prop :=
  ∀ x : ℝ, Real.exp 9401 < x →
    primeCounting x ^ (2 : ℕ) < Real.exp 1 * x / Real.log x * primeCounting (x / Real.exp 1)

end DudekPlatt.v4
