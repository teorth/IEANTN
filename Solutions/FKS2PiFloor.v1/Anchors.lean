/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Envelopes
import Quadrature
import LeanCert.Tactic.LeanCert

namespace FKS2PiFloor

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem lower_endpoint : (2.7 : ℝ) ≤ Real.exp 1 := by
  leancert (trust := kernel)

theorem upper_endpoint : Real.exp (6 : ℝ) < 404 := by
  leancert (trust := kernel)

theorem log_twenty_nine : (10 : ℝ) / 3 ≤ Real.log 29 := by
  leancert (trust := kernel)

theorem log_twenty_nine_bounds : (336729 : ℝ) / 100000 ≤ Real.log 29 ∧
    Real.log 29 ≤ 33673 / 10000 := by
  leancert (trust := kernel)

theorem lower_anchor : primitive 1 29 ≤ (116677 : ℝ) / 10000 := by
  have hl := log_twenty_nine_bounds.1
  calc
    primitive 1 29 = 29 / Real.log 29 + 29 / (Real.log 29) ^ 2 := by simp [primitive]
    _ ≤ 29 / (336729 / 100000) + 29 / (336729 / 100000 : ℝ) ^ 2 := by
      gcongr
    _ ≤ 116677 / 10000 := by norm_num

theorem upper_anchor : (116963 : ℝ) / 10000 - primitive (5 / 2) 29 ≤ -3.3 := by
  have hu := log_twenty_nine_bounds.2
  have hl : 0 < Real.log (29 : ℝ) := Real.log_pos (by norm_num)
  have hP : (149963 : ℝ) / 10000 ≤ primitive (5 / 2) 29 := by
    calc
      (149963 : ℝ) / 10000 ≤ 29 / (33673 / 10000) + (5 / 2) * 29 /
          (33673 / 10000 : ℝ) ^ 2 := by norm_num
      _ ≤ primitive (5 / 2) 29 := by
        unfold primitive
        gcongr
  linarith

theorem global_lower_bound {x : ℝ} (hx : 29 ≤ x) : primitive 1 x ≤ IEANTN.Li x := by
  have h := primitive_lower_bound (a := 29) (by norm_num) hx
  have hL := Li_29.1
  have ha := lower_anchor
  linarith

theorem global_upper_bound {x : ℝ} (hx : 29 ≤ x) :
    IEANTN.Li x ≤ primitive (5 / 2) x - 3.3 := by
  have h := primitive_upper_bound (a := 29) (by norm_num) hx log_twenty_nine
  have hU := Li_29.2
  have ha := upper_anchor
  linarith

end FKS2PiFloor
