/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.ChebyshevNumerics.v1.Conclusions
import IEANTN.Nodes.RosserSchoenfeld1962.v1.Conclusions

/-!
# Bridge: the finite Chebyshev check follows from equation (3.35)

`RosserSchoenfeld1962.v1.equation_3_35` is `ψ(x) < 1.03883 x` for every `x > 0`, and it has a
Comparator receipt. `ChebyshevNumerics.v1.psi_le_below_11723` is the weaker finite statement
`ψ(n) ≤ 1.11 n` for `n ≤ 11723`.

For `n = 0`, `ψ` vanishes. For `n ≥ 1`, `1.03883 n ≤ 1.11 n`, so the strict stronger bound
implies the weak one. This replaces the `native_decide` numerical assurance for that finite
range. It does not reprove equation (3.35).
-/

namespace IEANTN.Bridges.ChebyshevNumerics

theorem psi_le_below_11723_of_equation_3_35
    (h : RosserSchoenfeld1962.v1.equation_3_35) :
    ChebyshevNumerics.v1.psi_le_below_11723 := by
  intro n hn
  obtain rfl | hnpos := Nat.eq_zero_or_pos n
  · rw [Chebyshev.psi_zero]
    norm_num
  · have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hlt : Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := h (n : ℝ) hpos
    have hcoeff : (1.03883 : ℝ) * n ≤ 1.11 * n := by
      have : (1.03883 : ℝ) ≤ 1.11 := by norm_num
      exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
    change Chebyshev.psi (n : ℝ) ≤ 1.11 * (n : ℝ)
    exact le_trans hlt.le hcoeff

end IEANTN.Bridges.ChebyshevNumerics
