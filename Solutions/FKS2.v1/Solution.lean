/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Corollary22

/-!
# Solution: `FKS2.v1`

Proves the same declarations `Challenge.lean` states. Do **not** import the challenge module —
Comparator compares two modules declaring the same names, so importing it would collide.

This file holds the three compared theorems and nothing else. The development is in its sibling
files, which it imports:

* `Growth.lean` — when `x^{-a} (log x)^b exp(c √log x)` is decreasing. No primes; the cheapest part
  to finish and the right place to start.
* `PsiToTheta.lean` — Proposition 13 and Corollary 14.
* `ThetaToPi.lean` — Theorem 3, Corollary 23 and Corollary 26.

Splitting is for build time, not readability: Lake elaborates files in parallel and rebuilds only
what changed. See `progress.yaml`.

## The hypotheses are the point

Each theorem takes the node's imports as hypotheses. `PrimeNumberTheoremAnd`'s FKS2 development
threads the same facts as deliberate `sorry`s — it has no import mechanism, so its
`corollary_23_all` reports `sorryAx`. Here they arrive as arguments, which is what allows a
verified solution resting on exactly the same computations.

`FKS2Numerics.v1.table6_row2_floor` is the clearest case: upstream's `row2_floor`, a finite check
of `π` against `Li` on `[e, e⁶]`, left open there and imported here.
-/

/-! ### The two pipelines

Both are proved outright. They take no import hypotheses, because a conditional theorem quantified
over all admissible parameters consumes nothing from the network — which is exactly what makes them
verifiable now, ahead of the corollaries that need numerical inputs. -/

theorem FKS2.v1.challenge_proposition_13 : FKS2.v1.proposition_13 :=
  fun _ _ _ _ _ _ _ hR hA hB hx₀ ha₁ ha₂ hcmp hpsi ↦
    FKS2Sol.classicalBound_theta_of_psi hR hA hB hx₀ ha₁ ha₂ hcmp hpsi

theorem FKS2.v1.challenge_theorem_3 : FKS2.v1.theorem_3 :=
  fun _ _ _ _ _ _ hR hB hx₀ hA hC hCs hx₁ h ↦
    FKS2Sol.classicalBound_pi_of_theta hR hB hx₀ hA hC hCs hx₁ h

theorem FKS2.v1.challenge_corollary_14
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (bklnw_v1_corollary_5_1 : BKLNW.v1.corollary_5_1)
    (bklnw_v1_theta_error_le_one : BKLNW.v1.theta_error_le_one)
    (fks2numerics_v1_nu_asymp_e30_le : FKS2Numerics.v1.nu_asymp_e30_le)
    (fks2numerics_v1_theta_asymp_ge_one_below_e30 :
      FKS2Numerics.v1.theta_asymp_ge_one_below_e30) :
    FKS2.v1.corollary_14 :=
  FKS2Sol.corollary_14 fks_v1_psi_classical_bound bklnw_v1_corollary_5_1
    bklnw_v1_theta_error_le_one fks2numerics_v1_nu_asymp_e30_le
    fks2numerics_v1_theta_asymp_ge_one_below_e30

theorem FKS2.v1.challenge_corollary_22
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (bklnw_v1_corollary_5_1 : BKLNW.v1.corollary_5_1)
    (bklnw_v1_theta_error_le_one : BKLNW.v1.theta_error_le_one)
    (fks2numerics_v1_nu_asymp_e30_le : FKS2Numerics.v1.nu_asymp_e30_le)
    (fks2numerics_v1_theta_asymp_ge_one_below_e30 :
      FKS2Numerics.v1.theta_asymp_ge_one_below_e30)
    (fks2numerics_v1_corollary_22_mid_range : FKS2Numerics.v1.corollary_22_mid_range) :
    FKS2.v1.corollary_22 :=
  FKS2Sol.corollary_22 fks_v1_psi_classical_bound bklnw_v1_corollary_5_1
    bklnw_v1_theta_error_le_one fks2numerics_v1_nu_asymp_e30_le
    fks2numerics_v1_theta_asymp_ge_one_below_e30 fks2numerics_v1_corollary_22_mid_range

theorem FKS2.v1.challenge_corollary_23
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (buthe_v1_theorem_2_li_minus_pi : Buthe.v1.theorem_2_li_minus_pi)
    (fks2numerics_v1_table6_row2_floor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_23 :=
  FKS2Sol.corollary_23 fks_v1_psi_classical_bound buthe_v1_theorem_2_li_minus_pi
    fks2numerics_v1_table6_row2_floor

theorem FKS2.v1.challenge_corollary_26
    (fks_v1_psi_classical_bound : FKS.v1.psi_classical_bound)
    (buthe_v1_theorem_2_li_minus_pi : Buthe.v1.theorem_2_li_minus_pi) :
    FKS2.v1.corollary_26 :=
  FKS2Sol.corollary_26 fks_v1_psi_classical_bound buthe_v1_theorem_2_li_minus_pi
