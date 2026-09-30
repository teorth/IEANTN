/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import LeanCert.CertifiedBounds.Chebyshev
import RS12.Tables
open Chebyshev Real
namespace RS12Small
open LeanCert.Engine.Chebyshev.Psi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel verification of the fixed 600-input certificate uses exact rational arithmetic.
private theorem checks600 : checkAllPsiLeMulWith 600 (1038829 / 1000000) 20 = true := by
  decide +kernel

theorem small {x : ℝ} (hx : 0 < x) (h600 : x ≤ 600) : ψ x < RS_prime.c₀ * x := by
  have h := verify_all_psi_le_mul_real 600 20 (1038829 / 1000000)
    (by norm_num) checks600 x hx h600
  norm_num at h
  dsimp [RS_prime.c₀]
  nlinarith

-- Bridge for the finite square-root estimate: 600 exceeds (0.94 / 0.03883)^2.
private theorem sqrt_bridge {x : ℝ} (hx : 600 ≤ x)
    (h : |ψ x - x| ≤ 0.94 * sqrt x) : ψ x < RS_prime.c₀ * x := by
  have hs := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hn := Real.sqrt_nonneg x
  have hl : 24 < sqrt x := by nlinarith
  have ha := le_abs_self (ψ x - x)
  dsimp [RS_prime.c₀]
  nlinarith

-- Any explicit relative error less than the available margin suffices.
private theorem error_bridge {x ε : ℝ} (hx : 0 < x) (hε : ε < 0.03883)
    (h : |ψ x - x| ≤ ε * x) : ψ x < RS_prime.c₀ * x := by
  have := le_abs_self (ψ x - x)
  have := mul_lt_mul_of_pos_right hε hx
  dsimp [RS_prime.c₀]
  linarith
end RS12Small
