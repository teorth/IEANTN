/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Tactic

namespace RS12Factorial
open LeanCert.Core IntervalRat

/-- Transfer a rational upper endpoint, evaluated by the kernel, to a real logarithm. -/
private theorem log_le_of_endpoint {q u : ℚ} (hq : 0 < q)
    (hc : (logPointComputable q 20).hi ≤ u) : Real.log (q : ℝ) ≤ (u : ℝ) := by
  have hm := mem_logPointComputable hq 20
  exact hm.2.trans (by exact_mod_cast hc)

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
-- This fixed Taylor endpoint check is evaluated by the kernel using exact rationals.
theorem kernel_log_two : Real.log 2 ≤ 0.693148 := by
  have h := log_le_of_endpoint (q := 2) (u := 693148/1000000) (by norm_num)
    (by decide +kernel)
  norm_num at h ⊢
  exact h

set_option maxHeartbeats 0 in
-- This fixed Taylor endpoint check is evaluated by the kernel using exact rationals.
theorem kernel_log_three : Real.log 3 ≤ 1.098613 := by
  have h := log_le_of_endpoint (q := 3) (u := 1098613/1000000) (by norm_num)
    (by decide +kernel)
  norm_num at h ⊢
  exact h

set_option maxHeartbeats 0 in
-- This fixed Taylor endpoint check is evaluated by the kernel using exact rationals.
theorem kernel_log_five : Real.log 5 ≤ 1.609438 := by
  have h := log_le_of_endpoint (q := 5) (u := 1609438/1000000) (by norm_num)
    (by decide +kernel)
  norm_num at h ⊢
  exact h

set_option maxHeartbeats 0 in
-- This fixed Taylor endpoint check is evaluated by the kernel using exact rationals.
theorem kernel_log_seven : Real.log 7 ≤ 1.945911 := by
  have h := log_le_of_endpoint (q := 7) (u := 1945911/1000000) (by norm_num)
    (by decide +kernel)
  norm_num at h ⊢
  exact h

set_option maxHeartbeats 0 in
-- This fixed Taylor endpoint check is evaluated by the kernel using exact rationals.
theorem kernel_log_eleven : Real.log 11 ≤ 2.397896 := by
  have h := log_le_of_endpoint (q := 11) (u := 2397896/1000000) (by norm_num)
    (by decide +kernel)
  norm_num at h ⊢
  exact h

set_option maxHeartbeats 0 in
-- This fixed Taylor endpoint check is evaluated by the kernel using exact rationals.
theorem kernel_log_thirteen : Real.log 13 ≤ 2.564950 := by
  have h := log_le_of_endpoint (q := 13) (u := 2564950/1000000) (by norm_num)
    (by decide +kernel)
  norm_num at h ⊢
  exact h

end RS12Factorial
