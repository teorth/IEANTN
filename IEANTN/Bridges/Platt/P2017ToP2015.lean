/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.Platt2017.v1.Conclusions
import IEANTN.Nodes.Platt2015.v1.Conclusions

/-!
# Bridge: `Platt2017.v1` → `Platt2015.v1`

`Platt2017.v1` asserts the Riemann hypothesis up to `3.0610046 · 10¹⁰`; `Platt2015.v1` asserts it
up to `3.06 · 10¹⁰`. The first height is larger, and `RiemannHypothesisUpTo` is antitone in its
height — a verification that reaches further verifies everything a shorter one does — so the first
claim implies the second.

## Why this is worth a bridge rather than a remark

The two nodes are one computation reported in two papers, and the bridge is where that stops being
prose. The evidence:

* *Computing `π(x)` Analytically* says "We isolated all the zeros of `ζ` to a height of
  `30,610,046,000` (`103,800,788,359` zeros)", and cites for the technique a paper then in
  preparation under the title *Computing `ζ` on the half line* — which is what became *Isolating
  some non-trivial zeros of zeta*.
* That paper's abstract reports the same height, `≤ 30,610,046,000`.
* `KLN` records `N(H₀) = 103 800 788 359` at `H₀ = 3.0610046 · 10¹⁰` — the same zero count.

`MT` cites the first paper and rounds the height down to `3.06 · 10¹⁰`, which is why `Platt2015.v1`
states the weaker number: it exists to serve `MT`, and states what `MT` selected.

Both nodes carry their own first-hand justification, so this bridge is a *spare* ground rather than
the designated one. Its value is that the relationship is now checked on every push instead of
asserted in a note that could drift.
-/

namespace IEANTN.Bridges.Platt

open IEANTN

/-- `RiemannHypothesisUpTo` is antitone: verifying further verifies everything nearer. -/
theorem riemannHypothesisUpTo_mono {T T' : ℝ} (h : T' ≤ T) (hT : RiemannHypothesisUpTo T) :
    RiemannHypothesisUpTo T' :=
  ⟨fun s => hT.false ⟨s.1, s.2.1, Set.Icc_subset_Icc_right h s.2.2.1, s.2.2.2⟩⟩

/-- The verification to `3.0610046 · 10¹⁰` implies the one to `3.06 · 10¹⁰`. -/
theorem bridge_platt2017_to_platt2015 (h : Platt2017.v1.rh_up_to) : Platt2015.v1.rh_up_to :=
  riemannHypothesisUpTo_mono (by norm_num) h

end IEANTN.Bridges.Platt
