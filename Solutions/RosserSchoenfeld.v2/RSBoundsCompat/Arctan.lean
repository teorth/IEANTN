/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Linarith

/-!
Compatibility helpers for the pinned IEANTN environment. These two statements occur in Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Trigonometric/Bounds.lean.
The proofs below use the older non-strict le_tan theorem directly.

This file is a `module` because its one consumer, `HardyFirstZero.Phase`, is one, and a module
may import only modules.
-/

@[expose] public section

namespace RSBoundsCompat.Real

theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr hx) (Real.arctan_lt_pi_div_two x)

theorem self_le_arctan {x : ℝ} (hx : x ≤ 0) : x ≤ Real.arctan x := by
  have h := arctan_le_self (x := -x) (neg_nonneg.mpr hx)
  rw [Real.arctan_neg] at h
  linarith

end RSBoundsCompat.Real
