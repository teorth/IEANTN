/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import IEANTN.Nodes.RosserSchoenfeld1962.v6.Conclusions
import Port.HistoricalTheorem25

theorem RosserSchoenfeld1962.v6.challenge_theorem_25 :
    RosserSchoenfeld1962.v6.theorem_25 :=
  fun _ hx => RS5Historical.theorem25 hx
