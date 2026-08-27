/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.Wedeniwski.v1.Conclusions
-- for `riemannHypothesisUpTo_mono`; the closure rule permits a bridge to import another
import IEANTN.Bridges.Platt.P2017ToP2015

/-!
# Bridge: `Platt2017.v1` → `Wedeniwski.v1`

`Wedeniwski.v1` is the weakest evidence in the network: a claim on a website, unpublished, not peer
reviewed, with documented doubts about its error control and about what height it even claims. And
it is load-bearing — `Kadiri2005` takes its verification height from it, and the chain runs on from
there through `MT` and `FKS` to `FKS2`.

It does not have to stay that way. `Platt2017` verifies the Riemann hypothesis to
`3.0610046 · 10¹⁰`, which is nearly ten times `3 330 657 430.697`, using interval arithmetic and
through peer review. Since `RiemannHypothesisUpTo` is antitone in its height, that claim implies
this one outright.

## Why this is a spare rather than the designated ground

`Wedeniwski.v1` exists to record what `Kadiri2005` actually cited, and `Kadiri2005` cited the
ZetaGrid figure. Designating this bridge would quietly rewrite that history — the node would then
assert that its evidence is Platt's computation, which is not what happened in 2005.

What the bridge does instead is separate two questions that were previously tangled. *What did the
paper rely on?* — a website, and the designated justification still says so. *Is the claim true on
better evidence today?* — yes, and this is the proof, recompiled on every push. A reader asking how
much the `FKS2` chain really rests on a defunct website now gets the honest answer twice over: it
did, and it need not.
-/

namespace IEANTN.Bridges.Platt

open IEANTN

/-- The verification to `3.0610046 · 10¹⁰` implies the ZetaGrid height. -/
theorem bridge_platt2017_to_wedeniwski (h : Platt2017.v1.rh_up_to) : Wedeniwski.v1.rh_up_to :=
  riemannHypothesisUpTo_mono (by norm_num) h

end IEANTN.Bridges.Platt
