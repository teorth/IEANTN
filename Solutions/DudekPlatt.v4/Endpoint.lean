/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastián Rodrigo (AI-assisted)
-/
import Solution
import IEANTN.Bridges.DudekPlatt.V4ToV1

/-!
# `DudekPlatt.v4`: composed witness to the closed `.v1` endpoint

`Solution.lean` proves `DudekPlatt.v4`'s own challenge, conditional on `DudekPlatt.v3.criterion`
and `DudekPlattNumerics.v3.pi_two_sided_footnote`. `IEANTN.Bridges.DudekPlatt.V4ToV1` (core,
Conclusions-only) transports its conclusion to `DudekPlatt.v1`'s own literal printed statement.

Composing the two here, **inside this project's own `lake build`**, is what makes the composed
chain a durable, reproducible repository artifact rather than a one-off private check: it needs no
second solution project on the same `LEAN_PATH`, because `DudekPlatt.v4`'s own solution already
takes the footnote-parameter `π` estimate as a *hypothesis* (that is what its import edge on
`DudekPlattNumerics.v3.pi_two_sided_footnote` means) rather than as a proof term to be supplied
from `DudekPlattNumerics.v4`'s separate solution package. So this file sidesteps, rather than
needs to resolve, the module-name collision between the two packages that would arise from loading
both packages' `Solution` libraries in one process — see `Solutions/DudekPlattNumerics.v4`'s own
package for that separate, independently-built proof of the numerics hypothesis from
`MT.v2.corollary_1`, not composed into a single Lean term with this one for exactly that reason. -/

open IEANTN

/-- **The composed endpoint.** Dudek and Platt's own printed threshold `exp(9658)`
(`DudekPlatt.v1.ramanujan_inequality`), from the repaired criterion and the footnote-parameter
two-sided `π` estimate alone — no numerical certificate, and no dependence on the paper's own
defective Lemma 2.1. -/
theorem DudekPlatt.v4.closed_endpoint_v1
    (hcrit : DudekPlatt.v3.criterion)
    (hnum : DudekPlattNumerics.v3.pi_two_sided_footnote) :
    DudekPlatt.v1.ramanujan_inequality :=
  DudekPlatt.v4.ramanujan_inequality_of_9401_to_v1
    (DudekPlatt.v4.challenge_ramanujan_inequality_9401 hcrit hnum)
