/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.HalfPlane

/-!
Compatibility helpers for the pinned IEANTN environment. The theorem block is copied from Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Gamma/Deriv.lean:65-68.
Imports and the enclosing namespace are adapted for the older Mathlib pin.
-/
open Filter Set Real Asymptotics Complex
open scoped Topology

namespace RSBoundsCompat.Complex

theorem hasDerivAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt _root_.Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  apply (_root_.Complex.hasDerivAt_GammaIntegral hs).congr_of_eventuallyEq
  filter_upwards [(_root_.Complex.isOpen_re_gt 0).mem_nhds hs] with a using
    _root_.Complex.Gamma_eq_integral

end RSBoundsCompat.Complex
