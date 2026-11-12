/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import IEANTN.Nodes.RosserSchoenfeld1962.v2.Conclusions
import Max113.Proof

theorem RosserSchoenfeld1962.v2.challenge_psi_ratio_maximum_at_113
    (rosserschoenfeld1962_v1_equation_3_35 : RosserSchoenfeld1962.v1.equation_3_35) :
    RosserSchoenfeld1962.v2.psi_ratio_maximum_at_113 :=
  RS12Max113.ratio_maximum rosserschoenfeld1962_v1_equation_3_35

theorem RosserSchoenfeld1962.v2.challenge_psi_ratio_unique_maximum_at_113
    (rosserschoenfeld1962_v1_equation_3_35 : RosserSchoenfeld1962.v1.equation_3_35) :
    RosserSchoenfeld1962.v2.psi_ratio_unique_maximum_at_113 :=
  RS12Max113.ratio_unique_maximum rosserschoenfeld1962_v1_equation_3_35
