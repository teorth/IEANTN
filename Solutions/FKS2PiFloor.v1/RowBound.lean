/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Vocabulary.ErrorTerms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace FKS2PiFloor

noncomputable def row (x : ℝ) : ℝ :=
  0.826 * Real.sqrt (Real.sqrt (Real.log x / 5.5666305)) *
    Real.exp (-Real.sqrt (Real.log x / 5.5666305))

theorem admissibleBound_eq_row {x : ℝ} (hx : 1 ≤ x) :
    IEANTN.admissibleBound 0.826 0.25 1 5.5666305 x = row x := by
  have hy : 0 ≤ Real.log x / 5.5666305 :=
    div_nonneg (Real.log_nonneg hx) (by norm_num)
  have hquarter : (Real.log x / 5.5666305) ^ (0.25 : ℝ) =
      Real.sqrt (Real.sqrt (Real.log x / 5.5666305)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
    norm_num
  simp only [IEANTN.admissibleBound, row, hquarter, neg_mul, one_mul, Real.sqrt_eq_rpow]

theorem Epi_eq_abs_normalized {x : ℝ} (hx : 1 < x) :
    IEANTN.Eπ x = |(IEANTN.primeCounting x - IEANTN.Li x) * Real.log x / x| := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl : 0 < Real.log x := Real.log_pos hx
  simp [IEANTN.Eπ, abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hl,
    div_div_eq_mul_div]

theorem Epi_le_of_enclosures {x L U : ℝ} (hx : 1 < x)
    (hL : L ≤ IEANTN.Li x) (hU : IEANTN.Li x ≤ U)
    (hplus : (U - IEANTN.primeCounting x) * Real.log x / x ≤ row x)
    (hminus : (IEANTN.primeCounting x - L) * Real.log x / x ≤ row x) :
    IEANTN.Eπ x ≤ row x := by
  rw [Epi_eq_abs_normalized hx, abs_le]
  have hc : 0 ≤ Real.log x / x := by
    exact div_nonneg (Real.log_pos hx).le (lt_trans zero_lt_one hx).le
  have h1 := mul_le_mul_of_nonneg_right (sub_le_sub_left hL (IEANTN.primeCounting x)) hc
  have h2 := mul_le_mul_of_nonneg_right (sub_le_sub_right hU (IEANTN.primeCounting x)) hc
  simp only [mul_div_assoc] at hplus hminus ⊢
  constructor <;> nlinarith only [h1, h2, hplus, hminus]

end FKS2PiFloor
