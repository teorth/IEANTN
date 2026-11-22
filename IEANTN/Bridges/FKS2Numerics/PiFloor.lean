/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions
import IEANTN.Nodes.FKS2PiFloor.v1.Conclusions

/-! The isolated floor is the unchanged numerical conclusion. This bridge is deliberately
not designated until verification of the isolated node has produced a receipt. -/

namespace FKS2Numerics

/-- Transfer only the row-two small-range floor, not the node's other numerical claims. -/
theorem table6_row2_floor_of_pi_floor
    (h : FKS2PiFloor.v1.table6_row2_floor) : v1.table6_row2_floor := h

end FKS2Numerics
