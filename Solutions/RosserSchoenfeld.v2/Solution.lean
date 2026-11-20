/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.RosserSchoenfeld.v2.Conclusions
import Solution.FiniteRH
import RSBounds.RosserSchoenfeld1975

/-!
The finite-RH adapter uses Mathlib's conjugation and functional equation for zeta.
The published quartic proof then supplies the psi bound.
-/

namespace RosserSchoenfeld.v2

/-- The conditional psi estimate, with the exact network vocabulary and strict
constant, delegated to the published quartic proof after the proved RH bridge. -/
theorem challenge_psi_error_b23 : psi_error_b23 := by
  intro hRH x hx
  exact TernaryGoldbach.RSBounds.RosserSchoenfeld1975.psi_error_b23
    (finiteRH_of_network hRH) x hx

end RosserSchoenfeld.v2
