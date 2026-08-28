/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Corollary26

/-!
# Solution: `FKS2.v1`

The paper's four corollaries. Do **not** import the challenge module — Comparator compares two
modules declaring the same names, so importing it would collide.

## The pipelines are hypotheses now

Proposition 13 and Theorem 3 used to be lemmas in this solution. They are conclusions of `FKS2.v2`
now, so they arrive here as import hypotheses — which is exactly what `corollary_14` importing
`FKS2.v2.proposition_13` and `corollary_22` importing `FKS2.v2.theorem_3` means. The analysis that
proves them is in `Solutions/FKS2.v2`.

What is left here is instantiation and the numerical ranges: `Support.lean` for shared arithmetic,
`Dawson.lean` for the `D₊` bounds `corollary_22` needs, and one file per corollary.
-/

theorem FKS2.v1.challenge_corollary_14
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (bklnw_v1_corollary_5_1 : BKLNW.v1.corollary_5_1)
    (bklnw_v1_theta_error_le_one : BKLNW.v1.theta_error_le_one)
    (fks2numerics_v1_nu_asymp_e30_le : FKS2Numerics.v1.nu_asymp_e30_le)
    (fks2numerics_v1_theta_asymp_ge_one_below_e30 :
      FKS2Numerics.v1.theta_asymp_ge_one_below_e30)
    (fks2_v2_proposition_13 : FKS2.v2.proposition_13) :
    FKS2.v1.corollary_14 :=
  FKS2Sol.corollary_14 fks2_v2_proposition_13 fks_v1_psi_classical_bound
    bklnw_v1_corollary_5_1 bklnw_v1_theta_error_le_one fks2numerics_v1_nu_asymp_e30_le
    fks2numerics_v1_theta_asymp_ge_one_below_e30

theorem FKS2.v1.challenge_corollary_22
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (bklnw_v1_corollary_5_1 : BKLNW.v1.corollary_5_1)
    (bklnw_v1_theta_error_le_one : BKLNW.v1.theta_error_le_one)
    (fks2numerics_v1_nu_asymp_e30_le : FKS2Numerics.v1.nu_asymp_e30_le)
    (fks2numerics_v1_theta_asymp_ge_one_below_e30 :
      FKS2Numerics.v1.theta_asymp_ge_one_below_e30)
    (fks2numerics_v1_corollary_22_mid_range : FKS2Numerics.v1.corollary_22_mid_range)
    (fks2_v2_theorem_3 : FKS2.v2.theorem_3) :
    FKS2.v1.corollary_22 :=
  FKS2Sol.corollary_22 fks_v1_psi_classical_bound bklnw_v1_corollary_5_1
    bklnw_v1_theta_error_le_one fks2numerics_v1_nu_asymp_e30_le
    fks2numerics_v1_theta_asymp_ge_one_below_e30 fks2numerics_v1_corollary_22_mid_range
    fks2_v2_theorem_3

theorem FKS2.v1.challenge_corollary_23
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (buthe_v1_theorem_2_li_minus_pi : Buthe.v1.theorem_2_li_minus_pi)
    (fks2numerics_v1_table6_row2_floor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_23 :=
  FKS2Sol.corollary_23 fks_v1_psi_classical_bound buthe_v1_theorem_2_li_minus_pi
    fks2numerics_v1_table6_row2_floor

theorem FKS2.v1.challenge_corollary_26
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (buthe_v1_theorem_2_li_minus_pi : Buthe.v1.theorem_2_li_minus_pi)
    (fks2numerics_v1_table6_row2_floor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_26 :=
  FKS2Sol.corollary_26 fks_v1_psi_classical_bound buthe_v1_theorem_2_li_minus_pi
    fks2numerics_v1_table6_row2_floor
