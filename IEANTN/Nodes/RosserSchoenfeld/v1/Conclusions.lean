/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao

## A trap for whoever states the zero-free region

Theorem 1 of the paper is **not** of the shape `ClassicalZeroFreeRegion R`. It reads: there are no
zeros of `ζ` in the region `σ > 1 − 1/(R log|t/17|)` for `|t| ≥ 21`, with
`R = 9.645908801`. Two differences matter. The denominator is `log|t/17|`, not `log|t|`, which
makes the region *wider*; and the threshold is `|t| ≥ 21`, not `3`.

So restating it as `ClassicalZeroFreeRegion 9.645908801` would be an over-claim: it would assert
something on `3 ≤ t < 21` that the paper does not prove. Whoever states this conclusion should add
the `log|t/17|` shape to Vocabulary rather than force it into the existing one. `Kadiri2005.v1`
consumes exactly this theorem, so the shape is load-bearing, not cosmetic.

-/
import IEANTN.Vocabulary

/-!
# Node `RosserSchoenfeld.v1`

The classical source of explicit bounds on the Chebyshev functions, and the ancestor of every node
in this chain. Still cited for the inequalities its successors have not superseded.

**This node states nothing yet.** It records that the paper is in scope and carries its
citation, so that a conclusion can be added the moment a downstream node needs one.

What to add first:

Whichever inequalities downstream nodes actually cite, added one at a time. The paper contains a
great many, and transcribing them speculatively would be work without a consumer.
-/
