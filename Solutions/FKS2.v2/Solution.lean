/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import ThetaToPi

/-!
# Solution: `FKS2.v2`

The two pipelines, proved. Neither takes an import hypothesis: a conditional theorem quantified
over all admissible parameters consumes nothing from the network, which is exactly why this node
can be verified without waiting on any numerical input.

The development is in the sibling files — `Growth.lean` for the monotonicity toolkit,
`Dawson.lean` for `D₊`, `Integral.lean` for Lemma 12, `Stieltjes.lean` for partial summation, and
`PsiToTheta.lean` / `ThetaToPi.lean` for the two conversions themselves.
-/

theorem FKS2.v2.challenge_proposition_13 : FKS2.v2.proposition_13 :=
  fun _ _ _ _ _ _ _ hR hA hB hx₀ ha₁ ha₂ hcmp hpsi ↦
    FKS2Sol.classicalBound_theta_of_psi hR hA hB hx₀ ha₁ ha₂ hcmp hpsi

theorem FKS2.v2.challenge_theorem_3 : FKS2.v2.theorem_3 :=
  fun _ _ _ _ _ _ hR hB hx₀ hA hC hCs hx₁ h ↦
    FKS2Sol.classicalBound_pi_of_theta hR hB hx₀ hA hC hCs hx₁ h
