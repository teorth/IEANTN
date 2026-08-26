/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `FKBJ.v1`

Franke, Kleinjung, Büthe and Jost, *A practical analytic method for calculating `π(x)`*,
Math. Comp.

The computation of the zeros of `ζ` with imaginary part up to `10¹¹` that Büthe's analytic method
consumes. `Buthe.v1`'s Theorem 2 is the output of running that method on this data.

## What this node can and cannot say

Büthe's algorithm does not merely need to *know* that the Riemann hypothesis holds to some height —
it takes **the zeros themselves** as input, to a stated accuracy. That is data, not a proposition,
and the network has no way to state it: a conclusion is a `Prop`.

What is stateable, and what this node states, is the consequence: every zero up to `10¹¹` lies on
the critical line. Any consumer needs more than that, so the import edge into `Buthe.v1` records a
real dependency while understating it.

This is the first place the "a node is a claim" design meets a dependency that is genuinely a
*table of numbers*, and it is worth being explicit rather than pretending the edge is complete.
`Tables.lean` is the mechanism for data a statement is *made against*; data an external computation
consumed is a different thing again, and the network currently records it in prose.
-/

namespace FKBJ.v1

open IEANTN

/-- **The zeros to height `10¹¹`.** Every zero of `ζ` with real part strictly between `1/2` and `1`
and imaginary part in `[0, 10¹¹]` — there are none.

The stateable consequence of the zero computation reported in this paper, which Büthe describes as
the input to the bounds of his Theorem 2. See the module docstring: the computation supplies more
than this, and the surplus is not expressible as a `Prop`. -/
def rh_up_to : Prop :=
  RiemannHypothesisUpTo (10 ^ (11 : ℕ))

end FKBJ.v1
