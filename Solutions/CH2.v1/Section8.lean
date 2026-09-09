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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import Section7
import Mathlib.NumberTheory.LSeries.Dirichlet
import IEANTN.Nodes.ZetaLogDerivValues.v1.Conclusions

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

/-! ### The second segment of `𝓒_<`, from `-2+i` to `-∞+i`

Parametrised as `s(t) = (-2-t) + i` for `t ∈ (0, ∞)`, so `ds = -dt`. This is the one piece of the
contour where integrability cannot be dodged, since the interval is infinite.

The bound on `cot` is the companion of `lem:adamant`'s: on a horizontal line `Im z = y > 0`,

  `|cot z|² = (cos²x + sinh²y)/(sin²x + sinh²y) ≤ (1 + sinh²y)/sinh²y = coth²y`,

and at `y = π/2` the crude `coth y ≤ 1 + 1/y` of §7 gives `1 + 2/π`, which spares any numerical
evaluation of `cosh(π/2)`. The `t`-dependence is absorbed by `4 + t ≤ 4 e^{t/4}`, leaving a single
exponential integral. -/

/-- `|sin(x+iy)|² = sin²x + sinh²y`, the companion of `normSq_cos`. -/
theorem normSq_sin (z : ℂ) :
    Complex.normSq (Complex.sin z) = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  rw [hz, Complex.sin_add_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf
  have hc : Real.cosh z.im ^ 2 = 1 + Real.sinh z.im ^ 2 := by
    have := Real.sinh_sq z.im
    linarith
  nlinarith [Real.sin_sq_add_cos_sq z.re, hc]

/-- **`|cot z| ≤ coth y` on the horizontal line `Im z = y > 0`.** -/
theorem norm_cot_le_coth {z : ℂ} (hy : 0 < z.im) :
    ‖Complex.cot z‖ ≤ Real.cosh z.im / Real.sinh z.im := by
  have hs : 0 < Real.sinh z.im := Real.sinh_pos_iff.mpr hy
  have hsin : Complex.normSq (Complex.sin z) ≠ 0 := by
    rw [normSq_sin]
    positivity
  have hsin0 : Complex.sin z ≠ 0 := fun h ↦ hsin (by rw [h]; simp)
  have hsq : ‖Complex.cot z‖ ^ 2 ≤ (Real.cosh z.im / Real.sinh z.im) ^ 2 := by
    rw [Complex.cot_eq_cos_div_sin, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm,
      normSq_cos, normSq_sin, div_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcs := Real.sin_sq_add_cos_sq z.re
    have hch : Real.cosh z.im ^ 2 = 1 + Real.sinh z.im ^ 2 := by
      have := Real.sinh_sq z.im; linarith
    nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im),
      mul_nonneg (sq_nonneg (Real.sin z.re)) (sq_nonneg (Real.sinh z.im))]
  have h1 : (0 : ℝ) ≤ Real.cosh z.im / Real.sinh z.im := by positivity
  nlinarith [norm_nonneg (Complex.cot z), hsq, h1]

/-- The second segment of `𝓒_<`, from `-2+i` (at `t = 0`) to `-∞+i`. -/
noncomputable def segC2 (t : ℝ) : ℂ := ((-2 - t : ℝ) : ℂ) + Complex.I

theorem segC2_re (t : ℝ) : (segC2 t).re = -2 - t := by simp [segC2]

theorem segC2_im (t : ℝ) : (segC2 t).im = 1 := by simp [segC2]

theorem norm_segC2_sub_one_le {t : ℝ} (ht : 0 ≤ t) : ‖segC2 t - 1‖ ≤ 4 + t := by
  have h : segC2 t - 1 = ((-3 - t : ℝ) : ℂ) + Complex.I := by
    rw [segC2]; push_cast; ring
  rw [h]
  calc ‖((-3 - t : ℝ) : ℂ) + Complex.I‖ ≤ ‖((-3 - t : ℝ) : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
    _ = (3 + t) + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
          abs_of_nonpos (by linarith : (-3 - t : ℝ) ≤ 0)]
        ring
    _ = 4 + t := by ring

/-- `|(π/2) cot(πs/2)| ≤ (π/2)(1 + 2/π)` along the second segment, where `Im(πs/2) = π/2`. -/
theorem norm_cot_segC2_le (t : ℝ) :
    ‖Complex.cot ((Real.pi : ℂ) * segC2 t / 2)‖ ≤ 1 + 2 / Real.pi := by
  have hpi := Real.pi_pos
  have him : ((Real.pi : ℂ) * segC2 t / 2).im = Real.pi / 2 := by
    simp [Complex.mul_im, segC2_im, segC2_re]
  have h := norm_cot_le_coth (z := (Real.pi : ℂ) * segC2 t / 2) (by rw [him]; positivity)
  rw [him] at h
  refine le_trans h ?_
  have := CH2Section7.coth_le_one_add_inv (y := Real.pi / 2) (by positivity)
  calc Real.cosh (Real.pi / 2) / Real.sinh (Real.pi / 2) ≤ 1 + 1 / (Real.pi / 2) := this
    _ = 1 + 2 / Real.pi := by field_simp

/-- The integral over the second segment of `𝓒_<`; `ds = -dt` along the parametrisation. -/
noncomputable def intC2 (f : ℂ → ℂ) : ℂ := ∫ t in Set.Ioi (0:ℝ), -f (segC2 t)

/-- **The second segment's contribution.**

`4 + t ≤ 4 e^{t/4}` turns the whole integrand into a single exponential, so one application of
`integral_exp_mul_Ioi` finishes it. The result is `O(x^{-2}/log x)` — far below anything the
argument spends. -/
theorem norm_intC2_le {Φ : ℂ → ℂ}
    (hΦ : ∀ t ∈ Set.Ioi (0:ℝ), ‖Φ (segC2 t)‖ ≤ ‖segC2 t - 1‖)
    {x : ℝ} (hx : 15 ≤ x) :
    ‖intC2 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
      * (x : ℂ) ^ s)‖ ≤ 10.29 / (x ^ 2 * (Real.log x - 1 / 4)) := by
  have hpi := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : (2 : ℝ) < Real.log x := by
    have h1 : Real.log 15 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h2 : (2 : ℝ) < Real.log 15 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h := Real.exp_one_lt_d9
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [he]
      nlinarith [Real.exp_pos 1]
    linarith
  have ha : -(Real.log x - 1 / 4) < 0 := by linarith
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ),
      ‖-(((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * segC2 t / 2) * Φ (segC2 t)
        * (x : ℂ) ^ segC2 t)‖ ≤ 10.29 / x ^ 2 * Real.exp (-(Real.log x - 1 / 4) * t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hpihalf : ‖((Real.pi : ℂ) / 2)‖ = Real.pi / 2 := by
      rw [show ((Real.pi : ℝ) : ℂ) / 2 = (((Real.pi / 2 : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hxs : ‖(x : ℂ) ^ segC2 t‖ = 1 / x ^ 2 * Real.exp (-(Real.log x * t)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, segC2_re, Real.rpow_def_of_pos hx0,
        show Real.log x * (-2 - t) = -(2 * Real.log x) + -(Real.log x * t) by ring, Real.exp_add]
      have h2 : Real.exp (-(2 * Real.log x)) = 1 / x ^ 2 := by
        rw [show -(2 * Real.log x) = -(Real.log (x ^ 2)) by rw [Real.log_pow]; push_cast; ring,
          Real.exp_neg, Real.exp_log (by positivity), one_div]
      rw [h2]
    have hc := norm_cot_segC2_le t
    have hf : ‖Φ (segC2 t)‖ ≤ 4 + t := le_trans (hΦ t ht) (norm_segC2_sub_one_le ht0.le)
    have hexp : 4 + t ≤ 4 * Real.exp (t / 4) := by
      have := Real.add_one_le_exp (t / 4)
      linarith
    rw [norm_neg, norm_mul, norm_mul, norm_mul, hpihalf, hxs]
    have hcn : (0 : ℝ) ≤ ‖Complex.cot ((Real.pi : ℂ) * segC2 t / 2)‖ := norm_nonneg _
    have hfn : (0 : ℝ) ≤ ‖Φ (segC2 t)‖ := norm_nonneg _
    have hstep : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segC2 t / 2)‖ * ‖Φ (segC2 t)‖
        ≤ Real.pi / 2 * (1 + 2 / Real.pi) * (4 * Real.exp (t / 4)) := by
      have hA : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segC2 t / 2)‖
          ≤ Real.pi / 2 * (1 + 2 / Real.pi) := mul_le_mul_of_nonneg_left hc (by positivity)
      exact mul_le_mul hA (le_trans hf hexp) hfn (by positivity)
    have hpos : (0 : ℝ) ≤ 1 / x ^ 2 * Real.exp (-(Real.log x * t)) := by positivity
    have hfinal : Real.pi / 2 * (1 + 2 / Real.pi) * (4 * Real.exp (t / 4))
        * (1 / x ^ 2 * Real.exp (-(Real.log x * t)))
        ≤ 10.29 / x ^ 2 * Real.exp (-(Real.log x - 1 / 4) * t) := by
      have hcoef : Real.pi / 2 * (1 + 2 / Real.pi) * 4 ≤ 10.29 := by
        have heq : Real.pi / 2 * (1 + 2 / Real.pi) * 4 = 2 * Real.pi + 4 := by field_simp; ring
        rw [heq]
        have := Real.pi_lt_d6
        linarith
      have hexpeq : Real.exp (t / 4) * Real.exp (-(Real.log x * t))
          = Real.exp (-(Real.log x - 1 / 4) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hrw : Real.pi / 2 * (1 + 2 / Real.pi) * (4 * Real.exp (t / 4))
          * (1 / x ^ 2 * Real.exp (-(Real.log x * t)))
          = Real.pi / 2 * (1 + 2 / Real.pi) * 4 / x ^ 2
            * (Real.exp (t / 4) * Real.exp (-(Real.log x * t))) := by ring
      rw [hrw, hexpeq]
      have hxx : (0 : ℝ) < x ^ 2 := by positivity
      have hE : (0 : ℝ) < Real.exp (-(Real.log x - 1 / 4) * t) := Real.exp_pos _
      have hdiv : Real.pi / 2 * (1 + 2 / Real.pi) * 4 / x ^ 2 ≤ 10.29 / x ^ 2 := by gcongr
      nlinarith [hdiv, hE]
    nlinarith [hstep, hpos, hfinal,
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ Real.pi / 2) hcn) hfn]
  have hint : ‖intC2 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
      * (x : ℂ) ^ s)‖
      ≤ ∫ t in Set.Ioi (0:ℝ), 10.29 / x ^ 2 * Real.exp (-(Real.log x - 1 / 4) * t) := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t ↦ norm_nonneg _)
      ((integrableOn_exp_mul_Ioi ha 0).const_mul _) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpt t ht
  refine le_trans hint (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi ha 0]
  have hne : Real.log x - 1 / 4 ≠ 0 := by linarith
  field_simp
  norm_num

/-- **The `lem:ranadi` analogue**: the whole of `𝓒_<` contributes at most `18/x`.

The paper's bound is `(π²/4x)(2√2/log²x + (2+√2)/log³x + (1/√2)/log⁴x)`; this one keeps no powers
of `log x` at all, which the budget in `lem:hardin` absorbs many times over. See the note on the
first segment. -/
theorem norm_intClt_le {Φ : ℂ → ℂ}
    (hΦ1 : ∀ t ∈ Set.Icc (0:ℝ) (Real.sqrt 2), ‖Φ (segC1 t)‖ ≤ ‖segC1 t - 1‖)
    (hΦ2 : ∀ t ∈ Set.Ioi (0:ℝ), ‖Φ (segC2 t)‖ ≤ ‖segC2 t - 1‖)
    {x : ℝ} (hx : 15 ≤ x) :
    ‖intC1 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s * (x : ℂ) ^ s)
      + intC2 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
        * (x : ℂ) ^ s)‖ ≤ 18 / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : (2 : ℝ) < Real.log x := by
    have h1 : Real.log 15 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h2 : (2 : ℝ) < Real.log 15 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h := Real.exp_one_lt_d9
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he]
      nlinarith [Real.exp_pos 1]
    linarith
  have h1 := norm_intC1_le hΦ1 (by linarith : (1:ℝ) < x)
  have h2 := norm_intC2_le hΦ2 hx
  have hlast : 10.29 / (x ^ 2 * (Real.log x - 1 / 4)) ≤ 1 / x := by
    rw [div_le_div_iff₀ (by nlinarith) hx0]
    nlinarith
  calc ‖intC1 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
        * (x : ℂ) ^ s)
      + intC2 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
        * (x : ℂ) ^ s)‖ ≤ _ + _ := norm_add_le _ _
    _ ≤ 17 / x + 1 / x := add_le_add h1 (le_trans h2 hlast)
    _ = 18 / x := by ring

/-! ### `ζ'/ζ` on the real axis above `2`

`-ζ'/ζ(t) = ∑ Λ(n) n^{-t}` has non-negative terms, so its size is decreasing in `t`: the whole of
`[2,∞)` is controlled by the single value at `2`, which `ZetaLogDerivValues.v1` supplies.

Mathlib has every ingredient — `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
`ArithmeticFunction.vonMangoldt_nonneg`, and `LSeries.norm_term_le_of_re_le_re` — so only the
numerical value has to be imported. The one step needing care is that the sum of the *norms* at
`s = 2` is the norm of the sum, which holds because the terms there are non-negative reals; the
node's statement form, an existential producing a real `c` with `ζ'/ζ(2) = c`, is what makes that
available. -/

open ArithmeticFunction in
/-- At `s = 2` the terms of the Dirichlet series are non-negative reals. -/
theorem term_two_eq_ofReal_norm (n : ℕ) :
    LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ) n
      = ((‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ) n‖ : ℝ) : ℂ) := by
  rw [LSeries.norm_term_eq, LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [if_neg hn]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcast : ((n : ℂ)) ^ (2 : ℂ) = (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hn0]
      norm_num
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
    push_cast
    simp

open ArithmeticFunction in
/-- **`|ζ'/ζ(t)| ≤ 0.57` for every real `t ≥ 2`.**

Termwise from the Dirichlet series, with the base value imported from `ZetaLogDerivValues.v1`. The
constant is `0.57`, comfortably above the true `0.5699609931…`; nothing downstream is close enough
to the boundary for the rounding to matter. -/
theorem norm_logDeriv_zeta_le (hv : ZetaLogDerivValues.v1.logDeriv_two) {t : ℝ} (ht : 2 ≤ t) :
    ‖deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ)‖ ≤ 0.57 := by
  obtain ⟨c, hc, hceq⟩ := hv
  have hmargin : IEANTN.margin 0 = 1 := by simp [IEANTN.margin]
  rw [hmargin, one_mul] at hc
  have hcabs := abs_le.mp hc
  have hclo : c ≤ -0.569960 := by linarith [hcabs.2]
  have hchi : -0.569962 ≤ c := by linarith [hcabs.1]
  -- the two L-series
  have hret : (1 : ℝ) < ((t : ℂ)).re := by simp; linarith
  have hre2 : (1 : ℝ) < ((2 : ℂ)).re := by norm_num
  have hLt := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hret
  have hL2 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre2
  rw [neg_div, hceq] at hL2
  -- the norms at `s = 2` sum to `-c`
  have hsum2 : HasSum (fun n : ℕ ↦ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ) n‖) (-c) := by
    rw [← Complex.hasSum_ofReal]
    have h : HasSum (LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ))
        (LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ)) :=
      (LSeriesSummable_vonMangoldt hre2).hasSum
    have hval : LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ) = ((-c : ℝ) : ℂ) := by
      rw [hL2]; push_cast; ring
    rw [hval] at h
    exact h.congr_fun fun n ↦ (term_two_eq_ofReal_norm n).symm
  -- termwise comparison
  have hmono : ∀ n : ℕ, ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (t : ℂ) n‖
      ≤ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ) n‖ := by
    intro n
    refine LSeries.norm_term_le_of_re_le_re _ ?_ n
    simp
    linarith
  have hsumt : Summable fun n : ℕ ↦ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (t : ℂ) n‖ :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hmono hsum2.summable
  -- and the bound
  have hLtnorm : ‖LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) (t : ℂ)‖ ≤ -c := by
    rw [LSeries]
    refine le_trans (norm_tsum_le_tsum_norm hsumt) ?_
    rw [← hsum2.tsum_eq]
    exact Summable.tsum_le_tsum hmono hsumt hsum2.summable
  have hEq : ‖deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ)‖
      = ‖LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) (t : ℂ)‖ := by
    rw [hLt, neg_div, norm_neg]
  rw [hEq]
  linarith

/-! ### `Ã` on the segment from `1` to `-1`

`Ã(s) = -ζ'/ζ(s) - 1/(s-1)`, and on that segment the paper parametrises by `s = 1 - t`,
`t ∈ [0,2]`. The imported expansion collapses there: `s - 1 = -t` turns `(-1)^{n+1}aₙ(s-1)ⁿ` into
`-aₙtⁿ`, so

  `-Ã(1-t) = ∑ aₙ tⁿ`,   every `aₙ > 0`,   `a₀ = γ`.

That gives both facts `lem:arles` opens with — `Ã < 0` there, and a majorant. Since `tⁿ ≤ t·2^{n-1}`
for `n ≥ 1` and `t ∈ [0,2]`, the tail is at most `t(S - a₀)/2` with `S = ∑ aₙ2ⁿ = -Ã(-1)`, which the
second imported value pins.

**The majorant is `γ + 0.493 t`, where the paper's convexity argument gives a tangent line at
`t = 2`.** The two differ only in the slope; the leading `γ` — what `prop:coronidis` reports and
`lem:hardin` measures — is the same either way. -/

/-- `Ã(s) = -ζ'/ζ(s) - 1/(s-1)`, the integrand of `𝓒` with the pole at `1` removed. -/
noncomputable def Atilde (s : ℂ) : ℂ := -(deriv riemannZeta s / riemannZeta s) - 1 / (s - 1)

/-- **`-Ã(1-t) = ∑ aₙtⁿ` for `0 < t < 3`**, the imported expansion at `s = 1 - t`.

Returns the sum as a real, together with the fact that `Ã` there *is* its negative — which is what
makes `‖Ã(1-t)‖` computable rather than merely bounded. -/
theorem hasSum_Atilde_seg {a : ℕ → ℝ}
    (hsum : ∀ s : ℂ, s ≠ 1 → ‖s - 1‖ < 3 →
      HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1) * (a n : ℂ) * (s - 1) ^ n)
        (-(deriv riemannZeta s / riemannZeta s) - 1 / (s - 1)))
    {t : ℝ} (ht0 : 0 < t) (ht3 : t < 3) :
    ∃ V : ℝ, HasSum (fun n : ℕ ↦ a n * t ^ n) V ∧
      Atilde ((1 - t : ℝ) : ℂ) = ((-V : ℝ) : ℂ) := by
  have hne : ((1 - t : ℝ) : ℂ) ≠ 1 := by
    intro hcon
    have h : (1 : ℝ) - t = 1 := by exact_mod_cast hcon
    linarith
  have hlt : ‖((1 - t : ℝ) : ℂ) - 1‖ < 3 := by
    rw [show ((1 - t : ℝ) : ℂ) - 1 = ((-t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have H := hsum _ hne hlt
  have hterm : ∀ n : ℕ, (-1 : ℂ) ^ (n + 1) * (a n : ℂ) * (((1 - t : ℝ) : ℂ) - 1) ^ n
      = ((-(a n * t ^ n) : ℝ) : ℂ) := by
    intro n
    have h1 : (((1 - t : ℝ) : ℂ) - 1) = ((-t : ℝ) : ℂ) := by push_cast; ring
    have h4 : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [h1]
    push_cast
    rw [neg_pow, pow_succ]
    linear_combination (-(a n : ℂ) * (t : ℂ) ^ n) * h4
  have H2 : HasSum (fun n : ℕ ↦ ((-(a n * t ^ n) : ℝ) : ℂ)) (Atilde ((1 - t : ℝ) : ℂ)) :=
    H.congr_fun fun n ↦ (hterm n).symm
  have H3 : HasSum (fun n : ℕ ↦ -(a n * t ^ n)) (∑' n : ℕ, -(a n * t ^ n)) :=
    (Complex.summable_ofReal.mp H2.summable).hasSum
  refine ⟨-(∑' n : ℕ, -(a n * t ^ n)), ?_, ?_⟩
  · simpa using H3.neg
  · have h4 : ((∑' n : ℕ, -(a n * t ^ n) : ℝ) : ℂ) = Atilde ((1 - t : ℝ) : ℂ) := by
      rw [← H2.tsum_eq, ← Complex.ofReal_tsum]
    rw [← h4]
    push_cast
    ring

/-- `S = ∑ aₙ2ⁿ = ζ'/ζ(-1) - 1/2 ≤ 1.485055`, the slope's ingredient. -/
theorem hasSum_Atilde_two {a : ℕ → ℝ}
    (hsum : ∀ s : ℂ, s ≠ 1 → ‖s - 1‖ < 3 →
      HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1) * (a n : ℂ) * (s - 1) ^ n)
        (-(deriv riemannZeta s / riemannZeta s) - 1 / (s - 1)))
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one) :
    ∃ S : ℝ, S ≤ 1.485055 ∧ HasSum (fun n : ℕ ↦ a n * 2 ^ n) S := by
  obtain ⟨c, hc, hceq⟩ := hneg
  have hmargin : IEANTN.margin 0 = 1 := by simp [IEANTN.margin]
  rw [hmargin, one_mul] at hc
  have hcabs := abs_le.mp hc
  obtain ⟨V, hV, hVeq⟩ := hasSum_Atilde_seg hsum (t := 2) (by norm_num) (by norm_num)
  refine ⟨V, ?_, hV⟩
  have h1 : ((1 - (2 : ℝ) : ℝ) : ℂ) = -1 := by push_cast; ring
  rw [h1, Atilde, hceq] at hVeq
  have h2 : (1 : ℂ) / ((-1 : ℂ) - 1) = -(1 / 2 : ℂ) := by norm_num
  rw [h2] at hVeq
  have h3 : ((-V : ℝ) : ℂ) = ((-c + 1 / 2 : ℝ) : ℂ) := by rw [← hVeq]; push_cast; ring
  have h4 : -V = -c + 1 / 2 := by exact_mod_cast h3
  linarith [hcabs.2]

/-- **`‖Ã(1-t)‖ ≤ γ + 0.493 t` for `0 < t ≤ 2`.**

`-Ã(1-t) = ∑ aₙtⁿ` with `aₙ > 0`, so the value is `a₀` plus a tail at most `t(S - a₀)/2`; `a₀ = γ`
and `γ > 1/2` with `S ≤ 1.485055` give the slope. -/
theorem norm_Atilde_seg_le
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 2) :
    ‖Atilde ((1 - t : ℝ) : ℂ)‖ ≤ Real.eulerMascheroniConstant + 0.493 * t := by
  obtain ⟨a, hpos, ha0, hsum⟩ := hk
  obtain ⟨S, hS, hS2⟩ := hasSum_Atilde_two hsum hneg
  obtain ⟨V, hV, hVeq⟩ := hasSum_Atilde_seg hsum ht0 (by linarith)
  have hgam : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  -- shift both series past the leading term
  set G : ℕ → ℝ := fun n ↦ a n * t ^ n with hG
  set H : ℕ → ℝ := fun n ↦ a n * 2 ^ n with hH
  have hVs : HasSum (fun n : ℕ ↦ G (n + 1)) (V - a 0) := by
    rw [hasSum_nat_add_iff 1]
    simpa [hG] using hV
  have hSs : HasSum (fun n : ℕ ↦ H (n + 1)) (S - a 0) := by
    rw [hasSum_nat_add_iff 1]
    simpa [hH] using hS2
  have hcmp : ∀ n : ℕ, G (n + 1) ≤ t / 2 * H (n + 1) := by
    intro n
    simp only [hG, hH]
    have hpow : t ^ (n + 1) ≤ t * 2 ^ n := by
      have h : t ^ n ≤ 2 ^ n := pow_le_pow_left₀ ht0.le ht2 n
      calc t ^ (n + 1) = t * t ^ n := by rw [pow_succ]; ring
        _ ≤ t * 2 ^ n := by nlinarith [ht0.le]
    have hrw : t / 2 * (a (n + 1) * 2 ^ (n + 1)) = a (n + 1) * (t * 2 ^ n) := by
      rw [pow_succ]; ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hpow (hpos (n + 1)).le
  have htail : V - a 0 ≤ t / 2 * (S - a 0) := by
    rw [← hVs.tsum_eq, ← (hSs.mul_left (t / 2)).tsum_eq]
    refine Summable.tsum_le_tsum hcmp hVs.summable (hSs.mul_left (t / 2)).summable
  have hnorm : ‖Atilde ((1 - t : ℝ) : ℂ)‖ = V := by
    have hVnn : 0 ≤ V := by
      refine hV.nonneg fun n ↦ ?_
      have := (hpos n).le
      positivity
    rw [hVeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_neg]
  rw [hnorm, ← ha0]
  nlinarith [htail, hS, hgam, ht0.le, ha0 ▸ hgam]

end CH2Section8
