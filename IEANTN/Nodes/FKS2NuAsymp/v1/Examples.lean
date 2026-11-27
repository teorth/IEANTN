/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Vecchi
-/
import IEANTN.Nodes.FKS2NuAsymp.v1.Conclusions

/-!
# Examples: `FKS2NuAsymp.v1`

Consequences drawn from this node's conclusions, taken as hypotheses, to exhibit what each
statement buys without assuming it.
-/

namespace FKS2NuAsymp.v1.Examples

/-- The corrected bound `6.3381·10⁻⁷` still yields `Aθ = 121.0961` in FKS2's Corollary 14,
confirming that `FKS2.v1.corollary_14` can reroute onto `FKS2NuAsymp.v1.nu_asymp_e30_le`. -/
example (h : FKS2NuAsymp.v1.nu_asymp_e30_le) :
    (121.096 : ℝ) * (1 + FKS2Numerics.v1.nuAsympE30) ≤ 121.0961 := by
  unfold FKS2NuAsymp.v1.nu_asymp_e30_le at h
  simp only [IEANTN.margin, pow_zero, one_mul] at h
  linarith

/-- The refutation `nu_asymp_e30_gt` unfolds directly to the strict lower bound
`6.3376·10⁻⁷ < FKS2Numerics.v1.nuAsympE30`. -/
example (h : FKS2NuAsymp.v1.nu_asymp_e30_gt) :
    (6.3376e-7 : ℝ) < FKS2Numerics.v1.nuAsympE30 := by
  unfold FKS2NuAsymp.v1.nu_asymp_e30_gt FKS2Numerics.v1.nu_asymp_e30_le at h
  simp only [IEANTN.margin, pow_zero, one_mul, not_le] at h
  exact h

end FKS2NuAsymp.v1.Examples
