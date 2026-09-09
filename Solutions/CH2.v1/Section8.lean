/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Section 8: the integrals

§8 of Chirre–Helfgott (`sec:horint`, *The case of `Λ(n)`: Integrals*) bounds the two things
Theorem 1.1 leaves behind: the horizontal integral at `Im s = ±T`, and the integral over the
contour `𝓒` that runs from `1` to `-∞` under the non-trivial zeroes and over the trivial ones.
Its output is `lem:hardin`.

This file starts with §8.2, the contour, because it is the part that depends on nothing outside
the paper except the functional equation — and that is already a node, `ZetaLogDeriv.v1`.

## `lem:adamant`, and the shape it is used in

The contour `𝓒_<` leaves `-1` at `135°`, and the reason for that angle is `lem:adamant`: on the
line `Re z = -Im z`,

  `|cos z| ≥ 1`   and so   `|tan z| ≤ |z|`.

`45°` is the smallest angle at which the first of these holds, which is why the contour turns
where it does. The paper states it as `g(t) = tan(e^{3πi/4} t)` having `|g'| ≤ 1`; both forms are
here, since `lem:ranadi` uses the derivative bound and the value bound separately.

The proof of `|cos z| ≥ 1` is the identity `|cos(x+iy)|² = cos²x + sinh²y` together with
`|sin x| ≤ |x| = |y| ≤ |sinh y|`. The paper instead observes `cos u + cosh u ≥ 2` from the series;
the two come to the same thing, but `|sin| ≤ |·| ≤ |sinh|` is already in Mathlib.
-/

namespace CH2Section8

open scoped Real

/-- `|y| ≤ |sinh y|`: the companion of `|sin x| ≤ |x|`. -/
theorem abs_le_abs_sinh (y : ℝ) : |y| ≤ |Real.sinh y| := by
  rcases lt_trichotomy y 0 with h | h | h
  · have h1 : Real.sinh y < y := Real.sinh_lt_self_iff.mpr h
    have h2 : Real.sinh y < 0 := by
      have := Real.sinh_lt_sinh (x := y) (y := 0)
      simp only [Real.sinh_zero] at this
      exact this.mpr h
    rw [abs_of_neg h, abs_of_neg h2]
    linarith
  · simp [h]
  · have h1 : y < Real.sinh y := Real.self_lt_sinh_iff.mpr h
    have h2 : 0 < Real.sinh y := by linarith
    rw [abs_of_pos h, abs_of_pos h2]
    linarith

/-- `|cos(x+iy)|² = cos²x + sinh²y`. -/
theorem normSq_cos (z : ℂ) :
    Complex.normSq (Complex.cos z) = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  rw [hz, Complex.cos_add_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [Complex.re_add_im]
  have hc : Real.cosh z.im ^ 2 = 1 + Real.sinh z.im ^ 2 := by
    have := Real.sinh_sq z.im
    linarith
  nlinarith [Real.sin_sq_add_cos_sq z.re, hc]

/-- **`lem:adamant`, first half**: `|cos z| ≥ 1` on the line `Re z = -Im z`.

`|cos z|² = cos²x + sinh²y`, and with `|x| = |y|` we have `sinh²y ≥ y² = x² ≥ sin²x`. -/
theorem one_le_norm_cos {z : ℂ} (h : z.re = -z.im) : 1 ≤ ‖Complex.cos z‖ := by
  have hsq : (1 : ℝ) ≤ ‖Complex.cos z‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_cos]
    have h1 : |Real.sin z.re| ≤ |z.re| := Real.abs_sin_le_abs
    have h2 : |z.im| ≤ |Real.sinh z.im| := abs_le_abs_sinh z.im
    have h3 : |z.re| = |z.im| := by rw [h, abs_neg]
    have h4 : Real.sin z.re ^ 2 ≤ Real.sinh z.im ^ 2 := by
      have hs : |Real.sin z.re| ≤ |Real.sinh z.im| := by
        calc |Real.sin z.re| ≤ |z.re| := h1
          _ = |z.im| := h3
          _ ≤ |Real.sinh z.im| := h2
      nlinarith [abs_nonneg (Real.sin z.re), abs_nonneg (Real.sinh z.im),
        sq_abs (Real.sin z.re), sq_abs (Real.sinh z.im)]
    nlinarith [Real.sin_sq_add_cos_sq z.re]
  nlinarith [norm_nonneg (Complex.cos z)]

/-- The direction of `𝓒_<`'s first segment, `e^{3πi/4} = (-1+i)/√2`. -/
noncomputable def dir : ℂ := (-1 + Complex.I) / (Real.sqrt 2 : ℂ)

theorem dir_re_eq_neg_im : dir.re = -dir.im := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [dir]
  simp [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  ring

theorem norm_dir : ‖dir‖ = 1 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn2 : ‖(-1 + Complex.I : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hnum : ‖(-1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
    rw [← Real.sqrt_sq (norm_nonneg ((-1 : ℂ) + Complex.I)), hn2]
  rw [dir, norm_div, hnum, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2,
    div_self (ne_of_gt h2)]

/-- Every point of the ray has `Re = -Im`. -/
theorem dir_mul_re_eq_neg_im (t : ℝ) : (dir * (t : ℂ)).re = -(dir * (t : ℂ)).im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [dir_re_eq_neg_im]
  ring

/-- **`lem:adamant`, second half**: `|tan(e^{3πi/4} t)| ≤ |t|` for real `t`.

`tan` vanishes at `0`, and its derivative along the ray has norm `‖dir‖ / |cos|² ≤ 1`. -/
theorem norm_tan_dir_le (t : ℝ) : ‖Complex.tan (dir * (t : ℝ))‖ ≤ |t| := by
  have hcos : ∀ u : ℝ, Complex.cos (dir * (u : ℝ)) ≠ 0 := by
    intro u hcon
    have := one_le_norm_cos (dir_mul_re_eq_neg_im u)
    rw [hcon] at this
    simp at this
    linarith
  have hderiv : ∀ u : ℝ, HasDerivAt (fun v : ℝ ↦ Complex.tan (dir * (v : ℝ)))
      ((1 / Complex.cos (dir * (u : ℝ)) ^ 2) * dir) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ ↦ (dir * (v : ℂ))) dir u := by
      have := (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul dir
      simpa using this
    have h2 : HasDerivAt Complex.tan (1 / Complex.cos (dir * (u : ℝ)) ^ 2)
        (dir * (u : ℝ)) := Complex.hasDerivAt_tan (hcos u)
    exact h2.comp u h1
  have hbound : ∀ u : ℝ, ‖(1 / Complex.cos (dir * (u : ℝ)) ^ 2) * dir‖ ≤ 1 := by
    intro u
    rw [norm_mul, norm_dir, mul_one, norm_div, norm_one, norm_pow]
    have h := one_le_norm_cos (dir_mul_re_eq_neg_im u)
    rw [div_le_one (by positivity)]
    nlinarith
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v : ℝ ↦ Complex.tan (dir * (v : ℝ)))
    (f' := fun u : ℝ ↦ (1 / Complex.cos (dir * (u : ℝ)) ^ 2) * dir)
    (fun u _ ↦ (hderiv u).hasDerivWithinAt) (fun u _ ↦ hbound u) convex_univ
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa using key

end CH2Section8
