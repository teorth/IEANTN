/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Max113.Logs
import Mathlib.NumberTheory.Chebyshev

namespace RS12Max113
open Chebyshev
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A rational separator below the symbolic optimum, certified by an LCM comparison
and two Taylor logarithm intervals. -/
theorem psi_113_lower : (113 : ℝ) * 1.03882 < ψ 113 := by
  have hn : 12774 * 2 ^ 169 ≤ 10000 * Nat.lcmUpto 113 := by decide +kernel
  have hr : (12774 : ℝ) * 2 ^ 169 ≤ 10000 * (Nat.lcmUpto 113 : ℝ) := by exact_mod_cast hn
  have hb : (2 : ℝ)^169 * (12774 / 10000) ≤ Nat.lcmUpto 113 := by linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2^169 * (12774 / 10000)) hb
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow] at hl
  have h2 := Real.log_two_gt_d9
  have hq := Max113Logs.log_anchor_lower
  rw [show (113 : ℝ) = (113 : ℕ) by norm_num, psi_eq_log_lcmUpto]
  norm_num at hl
  linarith

end RS12Max113
