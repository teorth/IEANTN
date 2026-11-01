/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Port.RS13.Finite

namespace RS5Historical
open Real Chebyshev

private theorem sqrt361 : sqrt (361 : ℝ) = 19 := by norm_num

/-- Rosser–Schoenfeld (1962), Theorem 13: the quotient attains its global
maximum on the positive real axis at x=361. -/
theorem theorem13_maximum {x : ℝ} (hx : 0 < x) :
    (ψ x - θ x) / sqrt x ≤ (ψ 361 - θ 361) / sqrt 361 := by
  have ha := Theorem13.anchor_bounds
  have hc : 0 ≤ (ψ 361 - θ 361) / 19 := by linarith [ha.1]
  have hc7 : (7 / 5 : ℝ) ≤ (ψ 361 - θ 361) / 19 := by linarith [ha.1]
  have hb : ψ x - θ x ≤ ((ψ 361 - θ 361) / 19) * sqrt x := by
    by_cases hN : x ≤ 46656
    · apply Theorem13.finite_jump_bound hc hx hN
      intro n hn
      by_cases he : n = 361
      · subst n
        norm_num only [Nat.cast_ofNat, sqrt361]
        linarith
      · exact (Theorem13.finite_nonanchor hn he).trans
          (mul_le_mul_of_nonneg_right hc7 (sqrt_nonneg _))
    · exact (Theorem13.gap_large (le_of_not_ge hN)).le.trans
        (mul_le_mul_of_nonneg_right hc7 (sqrt_nonneg _))
  apply (div_le_iff₀ (sqrt_pos.2 hx)).2
  simpa only [sqrt361] using hb

/-- Rosser–Schoenfeld (1962), equation (3.36), with its exact strict constant. -/
theorem theorem13_bound {x : ℝ} (hx : 0 < x) :
    ψ x - θ x < 1.42620 * sqrt x := by
  have h := theorem13_maximum hx
  rw [sqrt361] at h
  have ha : (ψ 361 - θ 361) / 19 < (1.42620 : ℝ) := by
    linarith [Theorem13.anchor_bounds.2]
  have hb := (div_le_iff₀ (sqrt_pos.2 hx)).1 h
  exact hb.trans_lt (mul_lt_mul_of_pos_right ha (sqrt_pos.2 hx))

/-- Both assertions of the complete historical Theorem 13. -/
theorem theorem13 {x : ℝ} (hx : 0 < x) :
    (ψ x - θ x) / sqrt x ≤ (ψ 361 - θ 361) / sqrt 361 ∧
      ψ x - θ x < 1.42620 * sqrt x :=
  ⟨theorem13_maximum hx, theorem13_bound hx⟩

end RS5Historical
