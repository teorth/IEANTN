/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IntegralBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace FKS2PiFloor

noncomputable def primitive (k x : ℝ) : ℝ :=
  x / Real.log x + k * x / (Real.log x) ^ 2

theorem hasDerivAt_primitive (k : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (primitive k)
      (1 / Real.log x + ((k - 1) * Real.log x - 2 * k) / (Real.log x) ^ 3) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hl0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  convert (((hasDerivAt_id x).div (Real.hasDerivAt_log hx0) hl0).add
    (((hasDerivAt_id x).const_mul k).div
      ((Real.hasDerivAt_log hx0).pow 2) (pow_ne_zero 2 hl0))) using 1 <;>
    first | rfl | (simp only [Pi.pow_apply, id_eq]; field_simp; ring)

theorem lower_primitive_derivative {x : ℝ} (hx : 1 < x) :
    1 / Real.log x + ((1 - 1) * Real.log x - 2 * 1) / (Real.log x) ^ 3 ≤
      1 / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have : 0 ≤ 2 / (Real.log x) ^ 3 := by positivity
  simp only [sub_self, zero_mul, mul_one, zero_sub, neg_div]
  linarith

theorem upper_primitive_derivative {x : ℝ} (hx : (10 : ℝ) / 3 ≤ Real.log x) :
    1 / Real.log x ≤
      1 / Real.log x + (((5 : ℝ) / 2 - 1) * Real.log x - 2 * (5 / 2)) /
        (Real.log x) ^ 3 := by
  have hl : 0 < Real.log x := by linarith
  have hn : 0 ≤ ((5 : ℝ) / 2 - 1) * Real.log x - 2 * (5 / 2) := by linarith
  have : 0 ≤ (((5 : ℝ) / 2 - 1) * Real.log x - 2 * (5 / 2)) /
      (Real.log x) ^ 3 := div_nonneg hn (by positivity)
  linarith

theorem sub_le_sub_of_hasDerivAt_le {f g f' g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hg : ∀ y ∈ Set.Icc a b, HasDerivAt g (g' y) y)
    (hle : ∀ y ∈ Set.Icc a b, f' y ≤ g' y) :
    f b - f a ≤ g b - g a := by
  have hd : ∀ y ∈ Set.Icc a b,
      HasDerivAt (fun t ↦ g t - f t) (g' y - f' y) y :=
    fun y hy ↦ (hg y hy).sub (hf y hy)
  have hm : MonotoneOn (fun t ↦ g t - f t) (Set.Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy ↦ sub_nonneg.mpr (hle y (interior_subset hy)))
  have h := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  linarith

theorem primitive_lower_bound {a x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x) :
    primitive 1 x + (IEANTN.Li a - primitive 1 a) ≤ IEANTN.Li x := by
  have h := sub_le_sub_of_hasDerivAt_le hax
    (fun y hy ↦ hasDerivAt_primitive 1 (by linarith [hy.1]))
    (fun y hy ↦ hasDerivAt_Li (ha.trans hy.1))
    (fun y hy ↦ lower_primitive_derivative (by linarith [hy.1]))
  linarith

theorem primitive_upper_bound {a x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x)
    (hl : (10 : ℝ) / 3 ≤ Real.log a) :
    IEANTN.Li x ≤ primitive (5 / 2) x + (IEANTN.Li a - primitive (5 / 2) a) := by
  have h := sub_le_sub_of_hasDerivAt_le hax
    (fun y hy ↦ hasDerivAt_Li (ha.trans hy.1))
    (fun y hy ↦ hasDerivAt_primitive (5 / 2) (by linarith [hy.1]))
    (fun y hy ↦ upper_primitive_derivative
      (hl.trans (Real.log_le_log (by linarith) hy.1)))
  linarith

end FKS2PiFloor
