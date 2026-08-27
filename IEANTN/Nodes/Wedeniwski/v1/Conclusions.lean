/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `Wedeniwski.v1`

Wedeniwski, *The first 10 billion zeros of the Riemann zeta function are calculated and satisfy
the Riemann hypothesis*, the ZetaGrid distributed computation, `http://www.zetagrid.net`.

`Kadiri2005` takes its verification height from here: "pour `T₀`, nous prendrons la valeur de
S. Wedeniwski, c'est à dire très exactement `3 330 657 430.697`". That is the sole reason this node
exists, and the chain it feeds is long — `Wedeniwski → Kadiri2005 → MT → FKS → FKS2`.

## This node is the weakest evidence in the network, and that is the point of recording it

Its justification is `asserted`, not `numerical`, and the distinction is the one the network cares
most about: a `numerical` node states the outcome of a computation someone has described and stood
behind in a paper, while this is a claim on a website.

Platt and Trudgian set out the problem at length when superseding it. On reliability: the earlier
results "have the disadvantage that neither has been published in a peer reviewed journal.
Furthermore, it is not clear how the computations were set up to avoid problematic accumulation of
rounding and truncation errors. This concern was noted in works by Tao … and Helfgott." And on the
claim itself: "It is difficult to pinpoint the height claimed in these calculations" — different
slides from the same project give 200, 385, 561 and 900 billion zeros, implying heights from
`5.72 · 10¹⁰` to `2.41 · 10¹¹`.

Two things soften that here, and neither dissolves it. The height `Kadiri2005` uses,
`3.33 · 10⁹`, is far below any of the contested figures — it is the "first 10 billion zeros" of the
title, the earliest and least ambitious ZetaGrid claim. And it has since been comfortably
superseded: `Platt2017` verifies to `3.06 · 10¹⁰` and `PlattTrudgian` to `3 · 10¹²`, both with
interval arithmetic and both peer-reviewed.

**So the useful thing to do next is not to strengthen this node but to make it unnecessary.** A
bridge from `Platt2017.v1.rh_up_to` would discharge this conclusion outright, since
`3.0610046 · 10¹⁰` exceeds `3 330 657 430.697` and `RiemannHypothesisUpTo` is antitone. That would
move `Kadiri2005` off a website and onto a refereed computation without changing a single
statement. It is not done here only because `Kadiri2005`'s own justification is a citation of a
paper that used *this* height, and rewriting that history would be a different claim.
-/

namespace Wedeniwski.v1

open IEANTN

/-- **The ZetaGrid height.** The Riemann hypothesis holds up to `3 330 657 430.697`.

The figure is `Kadiri2005`'s, quoted as "très exactement" that value; the ZetaGrid project itself
reported a zero count rather than a height. See the module docstring for why this is `asserted`
rather than `numerical`, and for why superseding it is more useful than shoring it up. -/
def rh_up_to : Prop :=
  RiemannHypothesisUpTo 3330657430.697

end Wedeniwski.v1
