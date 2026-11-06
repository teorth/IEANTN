/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import IEANTN.Nodes.RosserSchoenfeld1962.v5.Conclusions
import Port.HistoricalEquation54

theorem RosserSchoenfeld1962.v5.challenge_equation_5_4 :
    RosserSchoenfeld1962.v5.equation_5_4 :=
  fun _ hx => RS5Historical.equation54 hx
