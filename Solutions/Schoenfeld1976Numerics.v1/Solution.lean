/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Nodes.Schoenfeld1976Numerics.v1.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v1.Conclusions
import Solution.FiniteRH
import Solution.Zeros
import RSBounds.PsiTable1976

/-!
# Solution: `Schoenfeld1976Numerics.v1`

The network's finite-RH predicate gives the RSBounds one (`Solution/FiniteRH.lean`, as in
`RosserSchoenfeld.v2`), and the three `ZetaZeroLocations.v1` statements give those of
`Zeros0to1000` (`Solution/Zeros.lean`). `RSBounds.PsiTable1976` then supplies the bound: the
quartic-smoothing proof of the 1975 row, with the explicit zeros taken up to height 1000.
-/

theorem Schoenfeld1976Numerics.v1.challenge_psi_error_b23
    (zetazerolocations_v1_located_0_1000 : ZetaZeroLocations.v1.located_0_1000)
    (zetazerolocations_v1_unique_0_1000 : ZetaZeroLocations.v1.unique_0_1000)
    (zetazerolocations_v1_count_0_1000 : ZetaZeroLocations.v1.count_0_1000) :
    Schoenfeld1976Numerics.v1.psi_error_b23 := by
  intro hRH x hx
  exact TernaryGoldbach.RSBounds.PsiTable1976.psi_error_of_zeros0to1000
    (Schoenfeld1976NumericsSolution.located_of zetazerolocations_v1_located_0_1000)
    (Schoenfeld1976NumericsSolution.unique_of zetazerolocations_v1_unique_0_1000)
    (Schoenfeld1976NumericsSolution.count_of zetazerolocations_v1_count_0_1000)
    (Schoenfeld1976NumericsSolution.finiteRH_of_network hRH) hx
