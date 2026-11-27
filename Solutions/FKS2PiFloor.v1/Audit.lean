/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Solution

open FKS2PiFloor FKS2PiFloor.Certificate
open LeanCert.Validity.IntegrationDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- The whole closed interval includes both endpoints.
example : IEANTN.Eπ (Real.exp 1) ≤ IEANTN.margin 0 *
    IEANTN.admissibleBound 0.826 0.25 1 5.5666305 (Real.exp 1) := by
  apply FKS2PiFloor.v1.challenge_table6_row2_floor
  exact ⟨le_rfl, Real.exp_le_exp.mpr (by norm_num)⟩

example : IEANTN.Eπ (Real.exp 6) ≤ IEANTN.margin 0 *
    IEANTN.admissibleBound 0.826 0.25 1 5.5666305 (Real.exp 6) := by
  apply FKS2PiFloor.v1.challenge_table6_row2_floor
  exact ⟨Real.exp_le_exp.mpr (by norm_num), le_rfl⟩

-- A prime right endpoint belongs to the next arithmetic cell.
example : IEANTN.primeCounting (11 : ℝ) = 5 := by
  exact primeCounting_eq_on_cell (a := 11) (b := 13) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

-- False integral bounds and an insufficient subdivision are rejected.
example : checkIntegralBoundsDyadicFull integrand (unitInterval 2) 64
    (120 / 100) (130 / 100) config = false := by decide +kernel

example : checkSplitCoreUpper (smallPlusCore 10 (51314 / 10000) 4) 10 11
    (by norm_num) 0 = false := by decide +kernel

/-- info: 'FKS2PiFloor.v1.challenge_table6_row2_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FKS2PiFloor.v1.challenge_table6_row2_floor
