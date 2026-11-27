/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Uniform
import IEANTN.Nodes.GammaAsymptotics.v1.Conclusions

/-!
# Solution: `GammaAsymptotics.v1`

The existing strip estimate supplies decay under positive integer translation. Telescoping the
recurrence with a uniform logarithmic increment estimate gives the half-plane bound with
constant `4`. The statement and its imported hypotheses are unchanged.

The strip estimate and its supporting Gauss-series development are Terence Tao's proof in
`Solutions/GammaAsymptotics.v2`, reused as the `GammaStrip` Lake library. No challenge is imported.
-/

theorem GammaAsymptotics.v1.challenge_digamma_sub_log_isBigO :
    GammaAsymptotics.v1.digamma_sub_log_isBigO :=
  ⟨4, fun _ hw ↦ GammaSolution.norm_digamma_sub_log_le hw⟩
