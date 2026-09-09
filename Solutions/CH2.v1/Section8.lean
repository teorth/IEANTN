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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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

/-! ### The first segment of `𝓒_<`, from `-1` to `-2+i`

Parametrised as `s(t) = -1 + e^{3πi/4} t` for `t ∈ [0, √2]`. Two facts make the estimate work:
`cot(w - π/2) = -tan w` moves `(π/2)cot(πs/2)` onto the ray through the origin, where
`lem:adamant` applies, and `Re s(t) = -1 - t/√2 ≤ -1` gives `|x^s| ≤ 1/x`.

**The bound here is cruder than the paper's `lem:ranadi`**, which integrates by parts repeatedly to
gain three powers of `log x`. That is not needed: what the contour estimate finally has to fit
inside is `lem:hardin`, where the whole of `prop:coronidis` is measured against
`(13 - 51/4) log T/log²x ≥ 3.45/log²x` while contributing only `γ/log²x ≈ 0.58` — a factor of five
in hand, and the `log³x` coefficient tolerates anything up to about `39` where the paper produces
`5/3`. Bounding the integrand by its maximum therefore suffices, and it avoids integrability
side-conditions entirely: `norm_integral_le_of_norm_le_const` needs none. -/

/-- The first segment of `𝓒_<`, from `-1` (at `t = 0`) to `-2+i` (at `t = √2`). -/
noncomputable def segC1 (t : ℝ) : ℂ := -1 + dir * (t : ℂ)

theorem segC1_re (t : ℝ) : (segC1 t).re = -1 - t / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : Real.sqrt 2 * (1 / 2) = 1 / Real.sqrt 2 := by
    field_simp
    nlinarith [hsq]
  rw [segC1, dir]
  simp [Complex.div_re, Complex.normSq_apply]
  field_simp
  linear_combination (-t) * hsq

/-- `|s(t) - 1| ≤ 2 + t`: the triangle inequality, since `‖dir‖ = 1`. -/
theorem norm_segC1_sub_one_le {t : ℝ} (ht : 0 ≤ t) : ‖segC1 t - 1‖ ≤ 2 + t := by
  have h : segC1 t - 1 = -2 + dir * (t : ℂ) := by rw [segC1]; ring
  rw [h]
  calc ‖(-2 : ℂ) + dir * (t : ℂ)‖ ≤ ‖(-2 : ℂ)‖ + ‖dir * (t : ℂ)‖ := norm_add_le _ _
    _ = 2 + t := by
        rw [norm_mul, norm_dir, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
        norm_num

/-- `cot(πs/2) = -tan(dir · (πt/2))` along the segment: `πs(t)/2 = dir·(πt/2) - π/2`. -/
theorem cot_segC1 (t : ℝ) :
    Complex.cot ((Real.pi : ℂ) * segC1 t / 2)
      = -Complex.tan (dir * ((Real.pi * t / 2 : ℝ) : ℂ)) := by
  have hw : (Real.pi : ℂ) * segC1 t / 2
      = dir * ((Real.pi * t / 2 : ℝ) : ℂ) - (Real.pi : ℂ) / 2 := by
    rw [segC1]
    push_cast
    ring
  rw [hw, Complex.cot_eq_cos_div_sin, Complex.cos_sub, Complex.sin_sub,
    Complex.cos_pi_div_two, Complex.sin_pi_div_two, Complex.tan_eq_sin_div_cos]
  simp only [mul_zero, mul_one, zero_add, zero_sub]
  rw [div_neg]

/-- `|(π/2) cot(πs/2)| ≤ π²t/4` along the segment, from `lem:adamant`. -/
theorem norm_cot_segC1_le {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.cot ((Real.pi : ℂ) * segC1 t / 2)‖ ≤ Real.pi * t / 2 := by
  have hpi := Real.pi_pos
  rw [cot_segC1, norm_neg]
  have h := norm_tan_dir_le (Real.pi * t / 2)
  rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi * t / 2)] at h

/-- The integral over the first segment of `𝓒_<`. -/
noncomputable def intC1 (f : ℂ → ℂ) : ℂ := ∫ t in (0:ℝ)..(Real.sqrt 2), f (segC1 t) * dir

/-- **The first segment's contribution**, bounded by the maximum of the integrand.

`(π²√2/4)(2+√2) · √2 < 17`, against the paper's `lem:ranadi`, which gains three powers of
`log x` by integrating by parts. See the section note for why the cruder constant is enough. -/
theorem norm_intC1_le {Φ : ℂ → ℂ}
    (hΦ : ∀ t ∈ Set.Icc (0:ℝ) (Real.sqrt 2), ‖Φ (segC1 t)‖ ≤ ‖segC1 t - 1‖)
    {x : ℝ} (hx : 1 < x) :
    ‖intC1 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
      * (x : ℂ) ^ s)‖ ≤ 17 / x := by
  have hpi := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lt : Real.sqrt 2 < 1.4143 := by nlinarith
  have hpilt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) (Real.sqrt 2),
      ‖((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * segC1 t / 2) * Φ (segC1 t)
        * (x : ℂ) ^ segC1 t * dir‖ ≤ 12 / x := by
    intro t ht
    rw [Set.uIoc_of_le hs2.le] at ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht.1
    have ht2 : t ≤ Real.sqrt 2 := ht.2
    have hmem : t ∈ Set.Icc (0:ℝ) (Real.sqrt 2) := ⟨ht0, ht2⟩
    have hc : ‖Complex.cot ((Real.pi : ℂ) * segC1 t / 2)‖ ≤ Real.pi * t / 2 :=
      norm_cot_segC1_le ht0
    have hf : ‖Φ (segC1 t)‖ ≤ 2 + t := le_trans (hΦ t hmem) (norm_segC1_sub_one_le ht0)
    have hxs : ‖(x : ℂ) ^ segC1 t‖ ≤ 1 / x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, segC1_re]
      rw [show (1 : ℝ) / x = x ^ (-1 : ℝ) by
        rw [Real.rpow_neg_one]; simp]
      refine Real.rpow_le_rpow_of_exponent_le hx.le ?_
      have : 0 ≤ t / Real.sqrt 2 := by positivity
      linarith
    have hpihalf : ‖((Real.pi : ℂ) / 2)‖ = Real.pi / 2 := by
      rw [show ((Real.pi : ℝ) : ℂ) / 2 = (((Real.pi / 2 : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_dir, mul_one, hpihalf]
    have h1 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    have hkey : Real.pi / 2 * (Real.pi * t / 2) * (2 + t) ≤ 12 := by
      have hb : t ≤ 1.4143 := le_trans ht2 hs2lt.le
      have hp2 : Real.pi ^ 2 ≤ 9.86961 := by nlinarith
      have hre : Real.pi / 2 * (Real.pi * t / 2) * (2 + t)
          = Real.pi ^ 2 / 4 * (t * (2 + t)) := by ring
      have ht2b : t * (2 + t) ≤ 1.4143 * (2 + 1.4143) := by nlinarith
      rw [hre]
      nlinarith [hp2, ht2b, ht0]
    have hprod : Real.pi / 2 * (Real.pi * t / 2) * (2 + t) * (1 / x) ≤ 12 / x := by
      rw [mul_one_div, div_le_div_iff₀ hx0 hx0]
      nlinarith [hkey, hx0]
    refine le_trans ?_ hprod
    have hfn := norm_nonneg (Φ (segC1 t))
    have hxn := norm_nonneg ((x : ℂ) ^ segC1 t)
    have hpt : (0 : ℝ) ≤ Real.pi / 2 * (Real.pi * t / 2) := by positivity
    have hA : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segC1 t / 2)‖
        ≤ Real.pi / 2 * (Real.pi * t / 2) := mul_le_mul_of_nonneg_left hc h1
    have hB : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segC1 t / 2)‖ * ‖Φ (segC1 t)‖
        ≤ Real.pi / 2 * (Real.pi * t / 2) * (2 + t) := mul_le_mul hA hf hfn hpt
    exact mul_le_mul hB hxs hxn (by positivity)
  have hkey := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := Real.sqrt 2)
    (f := fun t : ℝ ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * segC1 t / 2)
      * Φ (segC1 t) * (x : ℂ) ^ segC1 t * dir) hbound
  rw [intC1]
  refine le_trans hkey ?_
  rw [abs_of_pos (by linarith : (0:ℝ) < Real.sqrt 2 - 0)]
  have hfin : 12 / x * Real.sqrt 2 ≤ 17 / x := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hx0 hx0]
    nlinarith [hs2lt, hx0]
  linarith [hfin]

end CH2Section8
