/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Solution

/-! # Regression checks for the uniform estimate -/

-- The boundary is included at every height, with the same constant.
example (t : ℝ) :
    ‖Complex.digamma (1 + (t : ℂ) * Complex.I) - Complex.log (1 + (t : ℂ) * Complex.I)‖ ≤
      4 / ‖1 + (t : ℂ) * Complex.I‖ := by
  apply GammaSolution.norm_digamma_sub_log_le
  simp

/-- info: 'GammaAsymptotics.v1.challenge_digamma_sub_log_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GammaAsymptotics.v1.challenge_digamma_sub_log_isBigO
