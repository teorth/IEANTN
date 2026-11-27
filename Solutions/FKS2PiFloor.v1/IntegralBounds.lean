/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Endpoint-slope bounds for the offset logarithmic integral

These bounds use `IEANTN.Li x = ∫ t in 2..x, 1 / Real.log t`, not the
principal-value logarithmic integral `IEANTN.li`.
-/

namespace FKS2PiFloor

open MeasureTheory Set

/-- The integrand of the offset logarithmic integral is decreasing above `2`. -/
theorem antitoneOn_inv_log :
    AntitoneOn (fun t : ℝ ↦ 1 / Real.log t) (Ici 2) := by
  intro s hs t _ hst
  exact one_div_le_one_div_of_le (Real.log_pos (one_lt_two.trans_le hs))
    (Real.log_le_log (zero_lt_two.trans_le hs) hst)

/-- Integrability holds for either orientation of endpoints at least `2`. -/
theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t) volume a b := by
  apply AntitoneOn.intervalIntegrable
  apply antitoneOn_inv_log.mono
  intro t ht
  exact (le_min ha hb).trans ht.1

/-- The offset logarithmic integral has derivative `1 / log x`, including at `x = 2`. -/
theorem hasDerivAt_Li {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt IEANTN.Li (1 / Real.log x) x := by
  have hc : ∀ y ∈ Ioi (1 : ℝ), ContinuousAt (fun t : ℝ ↦ 1 / Real.log t) y := by
    intro y hy
    exact continuousAt_const.div
      (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans hy))) (Real.log_pos hy).ne'
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_inv_log le_rfl hx)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hc x (one_lt_two.trans_le hx))
    (hc x (one_lt_two.trans_le hx))

/-- Split the offset logarithmic integral at any other point at least `2`. -/
theorem Li_eq_add_integral {a x : ℝ} (ha : 2 ≤ a) (hx : 2 ≤ x) :
    IEANTN.Li x = IEANTN.Li a + ∫ t in a..x, 1 / Real.log t := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log le_rfl ha) (intervalIntegrable_inv_log ha hx)).symm

/-- The reciprocal logarithm at a right endpoint gives a lower slope bound. -/
theorem Li_add_div_log_le {a x b : ℝ} (ha : 2 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) :
    IEANTN.Li a + (x - a) / Real.log b ≤ IEANTN.Li x := by
  calc
    IEANTN.Li a + (x - a) / Real.log b =
        IEANTN.Li a + ∫ _ in a..x, 1 / Real.log b := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, one_mul]
    _ ≤ IEANTN.Li a + ∫ t in a..x, 1 / Real.log t := by
      apply add_le_add_right
      apply intervalIntegral.integral_mono_on hax intervalIntegrable_const
        (intervalIntegrable_inv_log ha (ha.trans hax))
      intro t ht
      exact antitoneOn_inv_log (ha.trans ht.1) (ha.trans (hax.trans hxb))
        (ht.2.trans hxb)
    _ = IEANTN.Li x := (Li_eq_add_integral ha (ha.trans hax)).symm

/-- The reciprocal logarithm at the left endpoint gives an upper slope bound. -/
theorem Li_le_add_div_log {a x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x) :
    IEANTN.Li x ≤ IEANTN.Li a + (x - a) / Real.log a := by
  calc
    IEANTN.Li x = IEANTN.Li a + ∫ t in a..x, 1 / Real.log t :=
      Li_eq_add_integral ha (ha.trans hax)
    _ ≤ IEANTN.Li a + ∫ _ in a..x, 1 / Real.log a := by
      apply add_le_add_right
      apply intervalIntegral.integral_mono_on hax
        (intervalIntegrable_inv_log ha (ha.trans hax)) intervalIntegrable_const
      intro t ht
      exact antitoneOn_inv_log ha (ha.trans ht.1) ht.1
    _ = IEANTN.Li a + (x - a) / Real.log a := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, one_mul]

/-- Both endpoint-slope bounds, valid including all coincident endpoints. -/
theorem Li_endpoint_slope_bounds {a x b : ℝ}
    (ha : 2 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) :
    IEANTN.Li a + (x - a) / Real.log b ≤ IEANTN.Li x ∧
      IEANTN.Li x ≤ IEANTN.Li a + (x - a) / Real.log a :=
  ⟨Li_add_div_log_le ha hax hxb, Li_le_add_div_log ha hax⟩

end FKS2PiFloor
