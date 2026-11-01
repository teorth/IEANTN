/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import IEANTN.Nodes.RosserSchoenfeld1962.v4.Conclusions
import Port.HistoricalTheorem13

theorem RosserSchoenfeld1962.v4.challenge_psi_sub_theta_ratio_maximum_at_361 :
    RosserSchoenfeld1962.v4.psi_sub_theta_ratio_maximum_at_361 :=
  fun _ hx => RS5Historical.theorem13_maximum hx

theorem RosserSchoenfeld1962.v4.challenge_equation_3_36 :
    RosserSchoenfeld1962.v4.equation_3_36 :=
  fun _ hx => RS5Historical.theorem13_bound hx
