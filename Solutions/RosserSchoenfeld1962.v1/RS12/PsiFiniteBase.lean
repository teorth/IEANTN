/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.PsiInteger
namespace RS12PsiInteger
open Chebyshev
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
-- Kernel verification of the fixed 600-input seed uses exact integer arithmetic.
private theorem psi_initial_check : checkPsiBlock 0 600 0 6919 = true := by
  decide +kernel
theorem psi_prefix_600 : ψ (600 : ℕ) ≤ (6919 : ℝ) * 693148 / 8000000 := by
  have h := checkPsiBlock_sound psi_initial_check (by simp [Chebyshev.psi])
  exact h.1
end RS12PsiInteger
