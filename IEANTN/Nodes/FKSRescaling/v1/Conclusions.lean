/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Node `FKSRescaling.v1`

`FKS.v1.rescaled_A_exceeds_printed` and `FKS.v1.rescaled_C_is_short_of_two`, split out so that
they can be proved on their own. A node is verified all at once, and the other two conclusions of
`FKS.v1` are the paper's analytic bounds on `Eψ`, so a proof of these two could not be a receipt
there.

The statements are copied unchanged. `FKS.v1`'s docstring on `psi_bound_all_x` explains what the
two gaps mean: rescaling Corollary 1.4 to `R = 5.5666305` does not give the printed classical
constants `A = 121.096` and `C = 2`, and both roundings go the strengthening way.
-/

namespace FKSRescaling.v1

/-- Rescaling the all-`x` bound into the `R = 5.5666305` shape overshoots the printed `A`,
copied from `FKS.v1.rescaled_A_exceeds_printed`.

`9.22022 · R^{3/2} = 121.09602174… > 121.096`. -/
def rescaled_A_exceeds_printed : Prop :=
  (9.22022 : ℝ) * (5.5666305 : ℝ) ^ ((3 : ℝ) / 2) > 121.096

/-- The matching gap in `C`, copied from `FKS.v1.rescaled_C_is_short_of_two`.

`0.8476836 · √R = 1.99999992… < 2`. -/
def rescaled_C_is_short_of_two : Prop :=
  (0.8476836 : ℝ) * Real.sqrt 5.5666305 < 2

end FKSRescaling.v1
