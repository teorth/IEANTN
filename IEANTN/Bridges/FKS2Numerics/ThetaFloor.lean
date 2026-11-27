/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions
import IEANTN.Nodes.FKS2ThetaFloor.v1.Conclusions

/-!
# Bridge: the proved theta floor implies `FKS2Numerics.v1.theta_asymp_ge_one_below_e30`

The two statements are the same proposition. This file is the record that proving the split node
discharges the numerical conclusion, and it is compiled by the core build.

It is not designated on `FKS2Numerics.v1` until `FKS2ThetaFloor.v1` has a receipt. Designating it
sooner would replace a numerical leaf by an unverified one.
-/

namespace FKS2Numerics

theorem theta_asymp_of_floor
    (h : FKS2ThetaFloor.v1.theta_asymp_ge_one_below_e30) :
    FKS2Numerics.v1.theta_asymp_ge_one_below_e30 := by
  simpa [FKS2ThetaFloor.v1.theta_asymp_ge_one_below_e30,
    FKS2Numerics.v1.theta_asymp_ge_one_below_e30] using h

end FKS2Numerics
