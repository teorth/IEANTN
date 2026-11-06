/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import RS12.Proof

namespace RS5Historical
open Real Chebyshev

/-- A clean substitute for the prime-power estimate in Lemma 13, obtained
from Theorem 12 and the three-term prime-power decomposition in mathlib. -/
theorem psi_sub_theta_le_prime_powers {x : ℝ} (hx : 1 ≤ x) :
    ψ x - θ x ≤ 1.03883 * x ^ (1 / 2 : ℝ) + 2.07766 * x ^ (1 / 3 : ℝ) := by
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h2 := RS_prime.theorem_12 (rpow_pos_of_pos hp (2 : ℝ)⁻¹)
  have h3 := RS_prime.theorem_12 (rpow_pos_of_pos hp (3 : ℝ)⁻¹)
  have h5 := RS_prime.theorem_12 (rpow_pos_of_pos hp (5 : ℝ)⁻¹)
  have h53 : x ^ (5 : ℝ)⁻¹ ≤ x ^ (3 : ℝ)⁻¹ :=
    rpow_le_rpow_of_exponent_le hx (by norm_num)
  have h := psi_sub_theta_le_psi_add_psi_add_psi x
  norm_num [RS_prime.c₀] at h2 h3 h5 ⊢
  linarith

end RS5Historical
