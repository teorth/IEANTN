/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `Platt2015.v1`

Platt, *Computing `π(x)` analytically*, Math. Comp. **84** (2015), 1521–1535.

The node exists for one reason: `MT`'s Theorem 1 consumes a height to which the Riemann hypothesis
has been verified, and names this paper as where that height was established. Without the node the
dependency could not be an edge, and `MT.v1.zero_free_region` had to be recorded as *not traced*
even though its sources were known.

Like `FKBJ.v1` and `PlattTrudgian.v1`, this states the *consequence* of a computation rather than
the computation. What the paper produced is a verified list of zeros; what the network can state is
that none of them lies off the critical line below the height reached. A node consuming the zeros
themselves — as `Büthe`'s algorithm does — needs more than this says.
-/

namespace Platt2015.v1

open IEANTN

/-- **The verification height.** The Riemann hypothesis holds up to `3.06 · 10¹⁰`.

`MT` §3 writes "We select `T₀ = 3.06 · 10¹⁰` as established in [10]", [10] being this paper, and
§2 explains what `T₀` is: "a height to which the Riemann hypothesis has been verified". That is
exactly this statement, and it is the whole of what `MT` takes from this paper. -/
def rh_up_to : Prop :=
  RiemannHypothesisUpTo 3.06e10

end Platt2015.v1
