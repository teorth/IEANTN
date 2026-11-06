/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import RS12.Proof

namespace RS5Historical
open Chebyshev

/-- Rosser–Schoenfeld (1962), equation (5.4), for every positive real x. -/
theorem equation54 {x : ℝ} (hx : 0 < x) : θ x < 1.11 * x := by
  have hc : RS_prime.c₀ < (1.11 : ℝ) := by norm_num [RS_prime.c₀]
  exact (theta_le_psi x).trans_lt
    ((RS_prime.theorem_12 hx).trans (mul_lt_mul_of_pos_right hc hx))

end RS5Historical
