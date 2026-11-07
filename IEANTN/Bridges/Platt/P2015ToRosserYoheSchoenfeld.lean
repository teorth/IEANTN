/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Nodes.RosserYoheSchoenfeld.v1.Conclusions
-- for `riemannHypothesisUpTo_mono`; the closure rule permits a bridge to import another
import IEANTN.Bridges.Platt.P2017ToP2015

/-!
# Bridge: `Platt2015.v1` → `RosserYoheSchoenfeld.v1`

`RosserYoheSchoenfeld.v1` states the Riemann hypothesis up to `1894438.5122`, the height at which
Rosser and Schoenfeld (1975) use the verification of the first `3 502 500` zeros. `Platt2015.v1`
verifies the Riemann hypothesis to `3.06 · 10¹⁰`. Since `RiemannHypothesisUpTo` is antitone in its
height, that claim implies this one.

## Why this is a spare rather than the designated ground

`RosserYoheSchoenfeld.v1` exists to record what the mid-1970s papers relied on, and they relied on
the computation of Rosser, Yohe and Schoenfeld. Designating this bridge would make the node assert
that its evidence is Platt's, which is not what those papers used. The bridge answers the other
question — is the statement true on today's evidence? — and is recompiled on every push.
-/

namespace IEANTN.Bridges.Platt

open IEANTN

/-- The verification to `3.06 · 10¹⁰` implies the Riemann hypothesis up to `1894438.5122`. -/
theorem bridge_platt2015_to_rosserYoheSchoenfeld (h : Platt2015.v1.rh_up_to) :
    RosserYoheSchoenfeld.v1.rh_up_to :=
  riemannHypothesisUpTo_mono (by norm_num) h

end IEANTN.Bridges.Platt
