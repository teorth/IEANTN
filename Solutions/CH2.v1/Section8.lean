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
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.ExponentialBounds
import Section7
import DigammaReal
import Mathlib.NumberTheory.LSeries.Dirichlet
import IEANTN.Nodes.ZetaLogDerivValues.v1.Conclusions
import IEANTN.Nodes.ZetaLogDeriv.v1.Conclusions
import IEANTN.Nodes.GammaAsymptotics.v2.Conclusions

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
theorem norm_logDeriv_zeta_le (hv : ZetaLogDerivValues.v1.logDeriv_two) {w : ℂ} (ht : 2 ≤ w.re) :
    ‖deriv riemannZeta w / riemannZeta w‖ ≤ 0.57 := by
  obtain ⟨c, hc, hceq⟩ := hv
  have hmargin : IEANTN.margin 0 = 1 := by simp [IEANTN.margin]
  rw [hmargin, one_mul] at hc
  have hcabs := abs_le.mp hc
  have hclo : c ≤ -0.569960 := by linarith [hcabs.2]
  have hchi : -0.569962 ≤ c := by linarith [hcabs.1]
  -- the two L-series
  have hret : (1 : ℝ) < w.re := by linarith
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
  have hmono : ∀ n : ℕ, ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) w n‖
      ≤ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (2 : ℂ) n‖ := by
    intro n
    refine LSeries.norm_term_le_of_re_le_re _ ?_ n
    norm_num
    linarith
  have hsumt : Summable fun n : ℕ ↦ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) w n‖ :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hmono hsum2.summable
  -- and the bound
  have hLtnorm : ‖LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) w‖ ≤ -c := by
    rw [LSeries]
    refine le_trans (norm_tsum_le_tsum_norm hsumt) ?_
    rw [← hsum2.tsum_eq]
    exact Summable.tsum_le_tsum hmono hsumt hsum2.summable
  have hEq : ‖deriv riemannZeta w / riemannZeta w‖
      = ‖LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) w‖ := by
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

/-! ### The horizontal contour from `-1` to `-∞`

By the functional equation, `Ã(s) + (π/2)cot(πs/2) = ζ'/ζ(t) + ψ(t) + 1/t - log 2π` with
`t = 1 - s`, and the right-hand side has no poles for `t ≥ 2` — which is the whole point of forking
the contour at `-1`. The integral is therefore stated in the `t` parametrisation from the start:
the left-hand side is a junk value at `s = -2, -4, …`, where both of its terms blow up and only the
sum is regular, while the right-hand side is honest everywhere on `[2, ∞)`.

Each piece of `g` is bounded separately: `|ζ'/ζ(t)| ≤ 0.57` from the imported value,
`|ψ(t) - log t| ≤ 1/t` from `DigammaReal`, `|1/t| ≤ 1/2`, and `|log(t/2π)| ≤ 2.15 + 0.16 t` from
`log u ≤ u - 1` applied both ways up. That gives `‖g(t)‖ ≤ 3.72 + 0.16 t`, and
`(3.72 + 0.16t)·t ≤ 8.08 e^{0.6u}` at `t = 2 + u` collapses the integral to a single exponential.

**Weaker than `lem:moruno`, which gets `-2Ã(-1)/(x log x) = 2.97/(x log x)`.** This gives `3.83/x`
at `x = 15` — a factor of three, in a term the budget does not notice. The paper's route needs the
concavity of `f(t) + 1/t` and the monotonicity of `t f(t)`, both from `lem:badabook`, whose proof
has an interval-arithmetic step on `[2,7]`; none of that is needed here. -/

/-- `g(t) = ζ'/ζ(t) + ψ(t) + 1/t - log 2π`, the integrand of the horizontal contour after the
functional equation, in the `t = 1 - s` parametrisation. -/
noncomputable def gfun (t : ℝ) : ℂ :=
  deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ) + Complex.digamma (t : ℂ)
    + 1 / (t : ℂ) - Complex.log (2 * (Real.pi : ℂ))

/-- `|log(t/2π)| ≤ 2.15 + 0.16 t` for `t ≥ 2`, from `log u ≤ u - 1` used in both directions. -/
theorem abs_log_sub_log_two_pi_le {t : ℝ} (ht : 2 ≤ t) :
    |Real.log t - Real.log (2 * Real.pi)| ≤ 2.15 + 0.16 * t := by
  have hpi := Real.pi_pos
  have hpi1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi2 : Real.pi < 3.141593 := Real.pi_lt_d6
  have ht0 : (0 : ℝ) < t := by linarith
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  have hup : Real.log t - Real.log (2 * Real.pi) ≤ 0.16 * t := by
    have h : Real.log (t / (2 * Real.pi)) ≤ t / (2 * Real.pi) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt ht0) (ne_of_gt h2pi)] at h
    have hb : t / (2 * Real.pi) ≤ 0.16 * t := by
      rw [div_le_iff₀ h2pi]
      nlinarith
    linarith
  have hdn : Real.log (2 * Real.pi) - Real.log t ≤ 2.15 := by
    have h : Real.log (2 * Real.pi / t) ≤ 2 * Real.pi / t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt h2pi) (ne_of_gt ht0)] at h
    have hb : 2 * Real.pi / t ≤ Real.pi := by
      rw [div_le_iff₀ ht0]
      nlinarith
    linarith
  rw [abs_le]
  have h0 : (0 : ℝ) ≤ 0.16 * t := by linarith
  constructor <;> linarith

/-- **`‖g(t)‖ ≤ 3.72 + 0.16 t` for real `t ≥ 2`.** -/
theorem norm_gfun_le (h2 : ZetaLogDerivValues.v1.logDeriv_two) {t : ℝ} (ht : 2 ≤ t) :
    ‖gfun t‖ ≤ 3.72 + 0.16 * t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hz := norm_logDeriv_zeta_le h2 (by simpa using ht : (2:ℝ) ≤ ((t : ℂ)).re)
  have hd := CH2Digamma.norm_digamma_sub_log_le ht0
  have hlog : Complex.log ((t : ℝ) : ℂ) = ((Real.log t : ℝ) : ℂ) :=
    (Complex.ofReal_log ht0.le).symm
  have hlog2 : Complex.log (2 * (Real.pi : ℂ)) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
    rw [show (2 : ℂ) * ((Real.pi : ℝ) : ℂ) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (by positivity)).symm
  have hinv : ‖(1 : ℂ) / ((t : ℝ) : ℂ)‖ = 1 / t := by
    rw [show (1 : ℂ) / ((t : ℝ) : ℂ) = (((1 / t : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsplit : gfun t = deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ)
      + (Complex.digamma (t : ℂ) - ((Real.log t : ℝ) : ℂ))
      + (((Real.log t - Real.log (2 * Real.pi) : ℝ)) : ℂ) + 1 / ((t : ℝ) : ℂ) := by
    rw [gfun, hlog2]
    push_cast
    ring
  have hlogbound : ‖(((Real.log t - Real.log (2 * Real.pi) : ℝ)) : ℂ)‖ ≤ 2.15 + 0.16 * t := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_log_sub_log_two_pi_le ht
  have hinvle : 1 / t ≤ 1 / 2 := by
    rw [div_le_div_iff₀ ht0 (by norm_num)]
    linarith
  have hdle : (1 : ℝ) / t ≤ 1 / 2 := hinvle
  rw [hsplit]
  calc ‖deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ)
        + (Complex.digamma (t : ℂ) - ((Real.log t : ℝ) : ℂ))
        + (((Real.log t - Real.log (2 * Real.pi) : ℝ)) : ℂ) + 1 / ((t : ℝ) : ℂ)‖
      ≤ ‖deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ)
          + (Complex.digamma (t : ℂ) - ((Real.log t : ℝ) : ℂ))
          + (((Real.log t - Real.log (2 * Real.pi) : ℝ)) : ℂ)‖ + ‖(1 : ℂ) / ((t : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ (‖deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ)
          + (Complex.digamma (t : ℂ) - ((Real.log t : ℝ) : ℂ))‖
          + ‖(((Real.log t - Real.log (2 * Real.pi) : ℝ)) : ℂ)‖) + ‖(1 : ℂ) / ((t : ℝ) : ℂ)‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((‖deriv riemannZeta (t : ℂ) / riemannZeta (t : ℂ)‖
          + ‖Complex.digamma (t : ℂ) - ((Real.log t : ℝ) : ℂ)‖)
          + ‖(((Real.log t - Real.log (2 * Real.pi) : ℝ)) : ℂ)‖) + ‖(1 : ℂ) / ((t : ℝ) : ℂ)‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((0.57 + 1 / t) + (2.15 + 0.16 * t)) + 1 / t := by
        rw [hinv]
        gcongr
    _ ≤ 3.72 + 0.16 * t := by linarith

/-- The horizontal contour from `-1` to `-∞`, parametrised by `t = 2 + u` with `u ∈ (0,∞)`, so that
`s = 1 - t = -1 - u` and `ds = -du`. -/
noncomputable def intHoriz (Φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ u in Set.Ioi (0:ℝ), -(gfun (2 + u) * Φ (2 + u) * ((x : ℂ) ^ ((-1 - u : ℝ) : ℂ)))

/-- **The horizontal contour's contribution**, the `lem:moruno` analogue.

`(3.72 + 0.16t)·t` at `t = 2 + u` is `8.08 + 4.36u + 0.16u²`, and `e^{0.6u} ≥ (1 + 0.3u)²` makes
that at most `8.08 e^{0.6u}`; one exponential integral then finishes it. -/
theorem norm_intHoriz_le (h2 : ZetaLogDerivValues.v1.logDeriv_two)
    {Φ : ℝ → ℂ} (hΦ : ∀ u ∈ Set.Ioi (0:ℝ), ‖Φ (2 + u)‖ ≤ 2 + u)
    {x : ℝ} (hx : 15 ≤ x) :
    ‖intHoriz Φ x‖ ≤ 8.08 / (x * (Real.log x - 0.6)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : (2 : ℝ) < Real.log x := by
    have h1 : Real.log 15 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h2' : (2 : ℝ) < Real.log 15 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h := Real.exp_one_lt_d9
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he]
      nlinarith [Real.exp_pos 1]
    linarith
  have ha : -(Real.log x - 0.6) < 0 := by linarith
  have hpt : ∀ u ∈ Set.Ioi (0:ℝ),
      ‖-(gfun (2 + u) * Φ (2 + u) * ((x : ℂ) ^ ((-1 - u : ℝ) : ℂ)))‖
        ≤ 8.08 / x * Real.exp (-(Real.log x - 0.6) * u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have ht : (2 : ℝ) ≤ 2 + u := by linarith
    have hg := norm_gfun_le h2 ht
    have hf := hΦ u hu
    have hxs : ‖(x : ℂ) ^ ((-1 - u : ℝ) : ℂ)‖ = 1 / x * Real.exp (-(Real.log x * u)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.ofReal_re]
      rw [Real.rpow_def_of_pos hx0,
        show Real.log x * (-1 - u) = -Real.log x + -(Real.log x * u) by ring, Real.exp_add]
      have h2' : Real.exp (-Real.log x) = 1 / x := by
        rw [Real.exp_neg, Real.exp_log hx0, one_div]
      rw [h2']
    have hexp : (8.08 : ℝ) + 4.36 * u + 0.16 * u ^ 2 ≤ 8.08 * Real.exp (0.6 * u) := by
      have h1 : (1 : ℝ) + 0.3 * u ≤ Real.exp (0.3 * u) := by
        have := Real.add_one_le_exp (0.3 * u)
        linarith
      have h2' : ((1 : ℝ) + 0.3 * u) ^ 2 ≤ Real.exp (0.3 * u) ^ 2 := by
        have hnn : (0 : ℝ) ≤ 1 + 0.3 * u := by linarith
        nlinarith [Real.exp_pos (0.3 * u)]
      have h3 : Real.exp (0.3 * u) ^ 2 = Real.exp (0.6 * u) := by
        rw [sq, ← Real.exp_add]
        ring_nf
      rw [h3] at h2'
      nlinarith [h2', sq_nonneg u]
    rw [norm_neg, norm_mul, norm_mul, hxs]
    have hgn : (0 : ℝ) ≤ ‖gfun (2 + u)‖ := norm_nonneg _
    have hfn : (0 : ℝ) ≤ ‖Φ (2 + u)‖ := norm_nonneg _
    have hstep : ‖gfun (2 + u)‖ * ‖Φ (2 + u)‖ ≤ (3.72 + 0.16 * (2 + u)) * (2 + u) :=
      mul_le_mul hg hf hfn (by linarith)
    have hpoly : (3.72 + 0.16 * (2 + u)) * (2 + u) = 8.08 + 4.36 * u + 0.16 * u ^ 2 := by ring
    rw [hpoly] at hstep
    have hpos : (0 : ℝ) ≤ 1 / x * Real.exp (-(Real.log x * u)) := by positivity
    have hfinal : 8.08 * Real.exp (0.6 * u) * (1 / x * Real.exp (-(Real.log x * u)))
        = 8.08 / x * Real.exp (-(Real.log x - 0.6) * u) := by
      rw [show (8.08 : ℝ) * Real.exp (0.6 * u) * (1 / x * Real.exp (-(Real.log x * u)))
          = 8.08 / x * (Real.exp (0.6 * u) * Real.exp (-(Real.log x * u))) by ring,
        ← Real.exp_add]
      congr 2
      ring
    calc ‖gfun (2 + u)‖ * ‖Φ (2 + u)‖ * (1 / x * Real.exp (-(Real.log x * u)))
        ≤ (8.08 * Real.exp (0.6 * u)) * (1 / x * Real.exp (-(Real.log x * u))) := by
          exact mul_le_mul_of_nonneg_right (le_trans hstep hexp) hpos
      _ = 8.08 / x * Real.exp (-(Real.log x - 0.6) * u) := hfinal
  have hint : ‖intHoriz Φ x‖
      ≤ ∫ u in Set.Ioi (0:ℝ), 8.08 / x * Real.exp (-(Real.log x - 0.6) * u) := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u ↦ norm_nonneg _)
      ((integrableOn_exp_mul_Ioi ha 0).const_mul _) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpt u hu
  refine le_trans hint (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi ha 0]
  have hne : Real.log x - 0.6 ≠ 0 := by linarith
  field_simp
  norm_num

/-! ### The initial segment of `𝓒`, from `1` to `-1`

`s(t) = 1 - t` on `[0,2]`, `ds = -dt`, so the integral is `-∫₀² Ã(1-t)Φ(1-t)x^{1-t} dt`. With
`‖Φ(1-t)‖ ≤ t` and `‖Ã(1-t)‖ ≤ γ + 0.493t` the integrand is at most `(γt + 0.493t²) x^{1-t}`, and
`γ(e^{λt} - 1) ≥ γλt ≥ 0.493t` for `λ = 0.986` folds the quadratic term into the exponential:

  `(γ + 0.493t)·t ≤ γ t e^{λt}`,   so the integral is at most `γx/(log x - λ)²`.

**`γ/(log x - λ)²` rather than `γ/log²x`**, which is where this parts company from `lem:arles`. The
difference is `γ(L² - (L-λ)²)/(L(L-λ)²) ≈ 2γλ/L² · (1/L)`, an extra `x/log³x` term with coefficient
about `2.3` — well inside what `lem:hardin` tolerates, and the leading `γ` is untouched.

The elementary antiderivative is used rather than the Gamma-function integral over `Ioi 0`: `∫₀²`
is a genuine interval integral here, and the fundamental theorem avoids every improper-integral
side condition. The discarded boundary term `-(2/r + 1/r²)e^{-2r}` is negative, so dropping it is
free. -/

/-- `∫₀² t e^{-rt} dt ≤ 1/r²`, by the elementary antiderivative. -/
theorem integral_mul_exp_le {r : ℝ} (hr : 0 < r) :
    ∫ t in (0:ℝ)..2, t * Real.exp (-(r * t)) ≤ 1 / r ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 2,
      HasDerivAt (fun u : ℝ ↦ -(u / r + 1 / r ^ 2) * Real.exp (-(r * u)))
        (t * Real.exp (-(r * t))) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ ↦ -(u / r + 1 / r ^ 2)) (-(1 / r)) t := by
      have h : HasDerivAt (fun u : ℝ ↦ u / r + 1 / r ^ 2) (1 / r) t := by
        simpa using ((hasDerivAt_id t).div_const r).add_const (1 / r ^ 2)
      exact h.neg
    have h2 : HasDerivAt (fun u : ℝ ↦ Real.exp (-(r * u))) (Real.exp (-(r * t)) * -r) t := by
      have hin : HasDerivAt (fun u : ℝ ↦ -(r * u)) (-r) t := by
        have h : HasDerivAt (fun u : ℝ ↦ r * u) r t := by
          simpa using (hasDerivAt_id t).const_mul r
        exact h.neg
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(r * t))).comp t hin
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ ↦ t * Real.exp (-(r * t))) MeasureTheory.volume 0 2 :=
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hexp : (0 : ℝ) < Real.exp (-(r * 2)) := Real.exp_pos _
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hnn : (0 : ℝ) ≤ (2 / r + 1 / r ^ 2) * Real.exp (-(r * 2)) := by positivity
  simp only [Real.exp_zero, mul_zero, neg_zero, zero_div, zero_add, mul_one]
  nlinarith [hnn]

/-- The initial segment of `𝓒`, from `1` (at `t = 0`) to `-1` (at `t = 2`); `ds = -dt`. -/
noncomputable def intSeg (Φ : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..2, -(Atilde ((1 - t : ℝ) : ℂ) * Φ ((1 - t : ℝ) : ℂ) * (x : ℂ) ^ ((1 - t : ℝ) : ℂ))

/-- **The initial segment's contribution**, the `lem:arles` analogue. -/
theorem norm_intSeg_le
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    {Φ : ℂ → ℂ} (hΦ : ∀ t ∈ Set.Icc (0:ℝ) 2, ‖Φ ((1 - t : ℝ) : ℂ)‖ ≤ t)
    {x : ℝ} (hx : 15 ≤ x) :
    ‖intSeg Φ x‖ ≤ Real.eulerMascheroniConstant * x / (Real.log x - 0.986) ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hgam : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hgam2 : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hL : (2 : ℝ) < Real.log x := by
    have h1 : Real.log 15 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h2' : (2 : ℝ) < Real.log 15 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h := Real.exp_one_lt_d9
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he]
      nlinarith [Real.exp_pos 1]
    linarith
  set r : ℝ := Real.log x - 0.986 with hrdef
  have hr : (0 : ℝ) < r := by rw [hrdef]; linarith
  -- the majorant
  have hbound : ∀ᵐ t : ℝ, t ∈ Set.Ioc (0:ℝ) 2 →
      ‖-(Atilde ((1 - t : ℝ) : ℂ) * Φ ((1 - t : ℝ) : ℂ) * (x : ℂ) ^ ((1 - t : ℝ) : ℂ))‖
        ≤ Real.eulerMascheroniConstant * x * (t * Real.exp (-(r * t))) := by
    filter_upwards with t ht
    obtain ⟨ht0, ht2⟩ := ht
    have hA := norm_Atilde_seg_le hk hneg ht0 ht2
    have hf := hΦ t ⟨ht0.le, ht2⟩
    have hxs : ‖(x : ℂ) ^ ((1 - t : ℝ) : ℂ)‖ = x * Real.exp (-(Real.log x * t)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.ofReal_re]
      rw [Real.rpow_def_of_pos hx0,
        show Real.log x * (1 - t) = Real.log x + -(Real.log x * t) by ring, Real.exp_add,
        Real.exp_log hx0]
    have hexp : (Real.eulerMascheroniConstant + 0.493 * t) * t
        ≤ Real.eulerMascheroniConstant * (t * Real.exp (0.986 * t)) := by
      have h1 : (1 : ℝ) + 0.986 * t ≤ Real.exp (0.986 * t) := by
        have := Real.add_one_le_exp (0.986 * t)
        linarith
      have hnn : (0 : ℝ) ≤ Real.eulerMascheroniConstant * t := by nlinarith [ht0.le]
      have h2 : Real.eulerMascheroniConstant * t * (1 + 0.986 * t)
          ≤ Real.eulerMascheroniConstant * t * Real.exp (0.986 * t) :=
        mul_le_mul_of_nonneg_left h1 hnn
      have h3 : (0 : ℝ) ≤ (Real.eulerMascheroniConstant - 1 / 2) * t ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg t)
      linarith [h2, h3]
    rw [norm_neg, norm_mul, norm_mul, hxs]
    have hAn : (0 : ℝ) ≤ ‖Atilde ((1 - t : ℝ) : ℂ)‖ := norm_nonneg _
    have hfn : (0 : ℝ) ≤ ‖Φ ((1 - t : ℝ) : ℂ)‖ := norm_nonneg _
    have hstep : ‖Atilde ((1 - t : ℝ) : ℂ)‖ * ‖Φ ((1 - t : ℝ) : ℂ)‖
        ≤ (Real.eulerMascheroniConstant + 0.493 * t) * t :=
      mul_le_mul hA hf hfn (by nlinarith [ht0.le])
    have hxpos : (0 : ℝ) ≤ x * Real.exp (-(Real.log x * t)) := by positivity
    have hcollapse : Real.eulerMascheroniConstant * (t * Real.exp (0.986 * t))
        * (x * Real.exp (-(Real.log x * t)))
        = Real.eulerMascheroniConstant * x * (t * Real.exp (-(r * t))) := by
      rw [show Real.eulerMascheroniConstant * (t * Real.exp (0.986 * t))
          * (x * Real.exp (-(Real.log x * t)))
          = Real.eulerMascheroniConstant * x * t
            * (Real.exp (0.986 * t) * Real.exp (-(Real.log x * t))) by ring,
        ← Real.exp_add, hrdef]
      have : (0.986 : ℝ) * t + -(Real.log x * t) = -((Real.log x - 0.986) * t) := by ring
      rw [this]
      ring
    calc ‖Atilde ((1 - t : ℝ) : ℂ)‖ * ‖Φ ((1 - t : ℝ) : ℂ)‖ * (x * Real.exp (-(Real.log x * t)))
        ≤ (Real.eulerMascheroniConstant * (t * Real.exp (0.986 * t)))
          * (x * Real.exp (-(Real.log x * t))) :=
          mul_le_mul_of_nonneg_right (le_trans hstep hexp) hxpos
      _ = Real.eulerMascheroniConstant * x * (t * Real.exp (-(r * t))) := hcollapse
  have hmajint : IntervalIntegrable
      (fun t : ℝ ↦ Real.eulerMascheroniConstant * x * (t * Real.exp (-(r * t))))
      MeasureTheory.volume 0 2 := Continuous.intervalIntegrable (by fun_prop) 0 2
  have hstep := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 2)
    hbound hmajint
  rw [intSeg]
  refine le_trans hstep ?_
  rw [intervalIntegral.integral_const_mul]
  have hI := integral_mul_exp_le hr
  have hcoef : (0 : ℝ) ≤ Real.eulerMascheroniConstant * x := by nlinarith
  calc Real.eulerMascheroniConstant * x * ∫ t in (0:ℝ)..2, t * Real.exp (-(r * t))
      ≤ Real.eulerMascheroniConstant * x * (1 / r ^ 2) :=
        mul_le_mul_of_nonneg_left hI hcoef
    _ = Real.eulerMascheroniConstant * x / r ^ 2 := by ring

/-! ### The three pieces together: the `prop:coronidis` arithmetic

The paper reports `γx/log²x + (5/3)x/log³x` for `x ≥ 15`. The three bounds above are

  `γx/(log x - 0.986)²`,   `18/x`,   `8.08/(x(log x - 0.6))`,

and putting them into that shape is where the `x ≥ 15` of the paper is not the natural range for
this route: at `x = 15` the second term alone needs the whole of the paper's `5/3`. **Stated for
`x ≥ 10⁶` instead**, which is the only range `lem:hardin` ever uses — it assumes `x ≥ T ≥ 10⁶` —
and there the constant comes out at `1.8` against the paper's `1.667`, with the leading `γ` exact.

The conversions all run through `log x ≤ 2√x`, which is `log u ≤ u - 1` at `u = √x`.

**What is still missing is the contour shift**, not the arithmetic: the paper's identity
`∫_𝓒 Ã Φ x^s ds = -∫_{𝓒_<} (π/2)cot(πs/2) Φ x^s ds + ∫_{-1}^{-∞}(Ã + (π/2)cot) Φ x^s ds`
is Cauchy's theorem applied to a function the functional equation makes holomorphic on the left
half-plane, and none of that is formalised here. So this bounds the *sum of the three pieces*, which
is what the decomposition produces, and identifying that sum with the integral over `𝓒` remains to
be done. -/

/-- `log x ≤ 2√x`, from `log u ≤ u - 1` at `u = √x`. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hsx
  rw [Real.log_sqrt hx.le] at h
  linarith

/-- `13 ≤ log x` for `x ≥ 10⁶`, since `e¹³ < 4.5 × 10⁵`. -/
theorem thirteen_le_log {x : ℝ} (hx : 1000000 ≤ x) : (13 : ℝ) ≤ Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.le_log_iff_exp_le hx0]
  have he : Real.exp 13 = Real.exp 1 ^ 13 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 : Real.exp 1 < 2.72 := by
    have := Real.exp_one_lt_d9
    linarith
  have h2 : Real.exp 1 ^ 13 < (2.72 : ℝ) ^ 13 :=
    pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
  have h3 : (2.72 : ℝ) ^ 13 < 1000000 := by norm_num
  rw [he]
  linarith

/-- **The `prop:coronidis` arithmetic**: the three pieces sum to `γx/log²x + 1.8x/log³x` for
`x ≥ 10⁶`, the range `lem:hardin` works in. -/
theorem coronidis_bound
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    {Φ : ℂ → ℂ} {Ψ : ℝ → ℂ}
    (hΦseg : ∀ t ∈ Set.Icc (0:ℝ) 2, ‖Φ ((1 - t : ℝ) : ℂ)‖ ≤ t)
    (hΦ1 : ∀ t ∈ Set.Icc (0:ℝ) (Real.sqrt 2), ‖Φ (segC1 t)‖ ≤ ‖segC1 t - 1‖)
    (hΦ2 : ∀ t ∈ Set.Ioi (0:ℝ), ‖Φ (segC2 t)‖ ≤ ‖segC2 t - 1‖)
    (hΨ : ∀ u ∈ Set.Ioi (0:ℝ), ‖Ψ (2 + u)‖ ≤ 2 + u)
    {x : ℝ} (hx : 1000000 ≤ x) :
    ‖intSeg Φ x‖
      + ‖intC1 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
            * (x : ℂ) ^ s)
          + intC2 (fun s ↦ ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) * Φ s
            * (x : ℂ) ^ s)‖
      + ‖intHoriz Ψ x‖
      ≤ Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx15 : (15 : ℝ) ≤ x := by linarith
  have hL13 : (13 : ℝ) ≤ Real.log x := thirteen_le_log hx
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hgam : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hgam2 : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  set s : ℝ := Real.sqrt x with hsdef
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs1000 : (1000 : ℝ) ≤ s := by
    rw [hsdef, show (1000 : ℝ) = Real.sqrt 1000000 by
      rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hLs : Real.log x ≤ 2 * s := log_le_two_mul_sqrt hx0
  have hL3 : Real.log x ^ 3 ≤ 8 * s ^ 3 := by
    have := pow_le_pow_left₀ hL0.le hLs 3
    nlinarith [this]
  -- the three pieces
  have hA := norm_intSeg_le hk hneg hΦseg hx15
  have hB := norm_intClt_le hΦ1 hΦ2 hx15
  have hC := norm_intHoriz_le h2v hΨ hx15
  -- and their conversions
  have hlam : (0 : ℝ) < Real.log x - 0.986 := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hkey1 : Real.eulerMascheroniConstant * Real.log x * 0.986 * (2 * Real.log x - 0.986)
      ≤ 1.6 * (Real.log x - 0.986) ^ 2 := by
    have hprod : (0 : ℝ) ≤ Real.log x * (2 * Real.log x - 0.986) := by nlinarith
    nlinarith [hL13, sq_nonneg (Real.log x - 13),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 / 3 - Real.eulerMascheroniConstant) hprod]
  have hconv1 : Real.eulerMascheroniConstant * x / (Real.log x - 0.986) ^ 2
      ≤ Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.6 * x / Real.log x ^ 3 := by
    have h1 : Real.eulerMascheroniConstant * x / (Real.log x - 0.986) ^ 2
        - Real.eulerMascheroniConstant * x / Real.log x ^ 2
        = Real.eulerMascheroniConstant * x * (0.986 * (2 * Real.log x - 0.986))
          / ((Real.log x - 0.986) ^ 2 * Real.log x ^ 2) := by
      field_simp
      ring
    have h2 : Real.eulerMascheroniConstant * x * (0.986 * (2 * Real.log x - 0.986))
        / ((Real.log x - 0.986) ^ 2 * Real.log x ^ 2) ≤ 1.6 * x / Real.log x ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hkey1
        (by positivity : (0:ℝ) ≤ x * Real.log x ^ 2)]
    linarith [h1, h2]
  have hconv2 : (18 : ℝ) / x ≤ 0.15 * x / Real.log x ^ 3 := by
    rw [div_le_div_iff₀ hx0 (by positivity)]
    have hxx : (0.15 : ℝ) * x * x = 0.15 * s ^ 4 := by rw [← hs2]; ring
    have hkey : (144 : ℝ) * s ^ 3 ≤ 0.15 * s ^ 4 := by nlinarith [hs1000, pow_pos hs0 3]
    rw [hxx]
    linarith [hL3, hkey]
  have hconv3 : (8.08 : ℝ) / (x * (Real.log x - 0.6)) ≤ 0.05 * x / Real.log x ^ 3 := by
    have hpos : (0 : ℝ) < x * (Real.log x - 0.6) := by nlinarith
    rw [div_le_div_iff₀ hpos (by positivity)]
    have hxsq : x * x = s ^ 4 := by rw [← hs2]; ring
    have hxx : (0.62 : ℝ) * s ^ 4 ≤ 0.05 * x * (x * (Real.log x - 0.6)) := by
      have heq : 0.05 * x * (x * (Real.log x - 0.6)) = 0.05 * s ^ 4 * (Real.log x - 0.6) := by
        linear_combination (0.05 * (Real.log x - 0.6)) * hxsq
      rw [heq]
      nlinarith [pow_pos hs0 4, hL13]
    have hkey : (64.64 : ℝ) * s ^ 3 ≤ 0.62 * s ^ 4 := by nlinarith [hs1000, pow_pos hs0 3]
    linarith [hL3, hkey, hxx]
  have hfinal : Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.6 * x / Real.log x ^ 3
      + 0.15 * x / Real.log x ^ 3 + 0.05 * x / Real.log x ^ 3
      = Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3 := by
    ring
  linarith [hA, hB, hC, hconv1, hconv2, hconv3, hfinal]

/-! ### The regular part is holomorphic on the left half-plane

The contour shift `prop:coronidis` performs — replacing `𝓒_<` by the real half-line for the part
of the integrand that has no poles there — rests on one analytic fact, and this is it.

`Ã(s) + (π/2)cot(πs/2)` has, as a Lean expression, poles at `s = -2, -4, …`, where both of its
terms blow up and only the sum is regular. **Written on the other side of the functional equation
it has none**: `ζ'/ζ(1-s) + ψ(1-s) + 1/(1-s) - log 2π` is holomorphic on all of `Re s < 0`, since
there `Re(1-s) > 1`, where `ζ` is non-vanishing and `ψ` is off its poles. That is the whole reason
the paper forks the contour at `-1` and shifts only this piece.

`deriv riemannZeta` and `deriv Gamma` are differentiable because their functions are *analytic* —
differentiable on an open set — which is where `DifferentiableOn.analyticOnNhd` and `AnalyticAt.deriv`
come in; differentiability alone would not give it.

**What this does not do is the shift itself.** Cauchy's theorem for the region between `𝓒_<` and the
real half-line, together with the vanishing of the cap at `-∞`, is not formalised here. -/

/-- `ζ'/ζ` is holomorphic where `Re s > 1`. -/
theorem differentiableAt_logDeriv_zeta {w : ℂ} (hw : 1 < w.re) :
    DifferentiableAt ℂ (fun v : ℂ ↦ deriv riemannZeta v / riemannZeta v) w := by
  have hne : w ≠ 1 := by
    intro h
    rw [h] at hw
    simp at hw
  have hζd : DifferentiableOn ℂ riemannZeta {v : ℂ | v ≠ 1} := fun v hv ↦
    (differentiableAt_riemannZeta hv).differentiableWithinAt
  have hζa : AnalyticAt ℂ riemannZeta w := hζd.analyticOnNhd isOpen_ne w hne
  exact (hζa.deriv.differentiableAt).div (differentiableAt_riemannZeta hne)
    (riemannZeta_ne_zero_of_one_lt_re hw)

/-- `ψ` is holomorphic on the right half-plane. -/
theorem differentiableAt_digamma {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.digamma w := by
  have hpole : ∀ v : ℂ, 0 < v.re → ∀ m : ℕ, v ≠ -(m : ℂ) := by
    intro v hv m hcon
    rw [hcon] at hv
    simp only [Complex.neg_re, Complex.natCast_re] at hv
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓd : DifferentiableOn ℂ Complex.Gamma {v : ℂ | 0 < v.re} := fun v hv ↦
    (Complex.differentiableAt_Gamma v (hpole v hv)).differentiableWithinAt
  have hΓa : AnalyticAt ℂ Complex.Gamma w := hΓd.analyticOnNhd hopen w hw
  show DifferentiableAt ℂ (fun v : ℂ ↦ deriv Complex.Gamma v / Complex.Gamma v) w
  exact (hΓa.deriv.differentiableAt).div hΓa.differentiableAt (Complex.Gamma_ne_zero (hpole w hw))

/-- The regular part of the contour integrand, on the right-hand side of the functional equation:
`G(s) = ζ'/ζ(1-s) + ψ(1-s) + 1/(1-s) - log 2π`. -/
noncomputable def Gfun (s : ℂ) : ℂ :=
  deriv riemannZeta (1 - s) / riemannZeta (1 - s) + Complex.digamma (1 - s)
    + 1 / (1 - s) - Complex.log (2 * (Real.pi : ℂ))

/-- **`G` is holomorphic on `Re s < 0`.** -/
theorem differentiableOn_Gfun : DifferentiableOn ℂ Gfun {s : ℂ | s.re < 0} := by
  intro s hs
  have hs' : s.re < 0 := hs
  have hre : 1 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hne0 : (1 : ℂ) - s ≠ 0 := by
    intro hcon
    have : (1 - s).re = 0 := by rw [hcon]; simp
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have hinner : DifferentiableAt ℂ (fun v : ℂ ↦ 1 - v) s := by
    simpa using (differentiableAt_id (𝕜 := ℂ) (x := s)).const_sub (1 : ℂ)
  have h1 : DifferentiableAt ℂ (fun v : ℂ ↦ deriv riemannZeta (1 - v) / riemannZeta (1 - v)) s := by
    simpa [Function.comp_def] using (differentiableAt_logDeriv_zeta hre).comp s hinner
  have h2 : DifferentiableAt ℂ (fun v : ℂ ↦ Complex.digamma (1 - v)) s := by
    simpa [Function.comp_def] using
      (differentiableAt_digamma (by linarith : (0 : ℝ) < (1 - s).re)).comp s hinner
  have h3 : DifferentiableAt ℂ (fun v : ℂ ↦ 1 / (1 - v)) s :=
    DifferentiableAt.div (differentiableAt_const (1 : ℂ)) hinner hne0
  exact (((h1.add h2).add h3).sub_const _).differentiableWithinAt

/-- `cos(π(1-s)/2) = sin(πs/2)`. -/
theorem cos_pi_one_sub_div_two (s : ℂ) :
    Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = Complex.sin ((Real.pi : ℂ) * s / 2) := by
  rw [show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring,
    Complex.cos_sub, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- `tan(π(1-s)/2) = cot(πs/2)`, the identity that turns the functional equation's `tan` into the
`cot` the contour integrand carries. -/
theorem tan_pi_one_sub_div_two (s : ℂ) :
    Complex.tan ((Real.pi : ℂ) * (1 - s) / 2) = Complex.cot ((Real.pi : ℂ) * s / 2) := by
  rw [show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring,
    Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin, Complex.sin_sub, Complex.cos_sub,
    Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring_nf

/-- **`G(s) = Ã(s) + (π/2)cot(πs/2)` on `Re s < 0`**, wherever the right-hand side is not a junk
value.

This is the functional equation, imported from `ZetaLogDeriv.v1` and applied at `1 - s`. The
hypothesis `sin(πs/2) ≠ 0` excludes exactly the even integers `s = -2, -4, …`, which are precisely
the points where `cot(πs/2)` and `Ã` both blow up and their sum does not — so it is the guard that
keeps the right-hand side honest, and it costs nothing, those points being where the contour
integral does not care. -/
theorem Gfun_eq (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    {s : ℂ} (hs : s.re < 0) (hsin : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0) :
    Gfun s = Atilde s + ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * s / 2) := by
  have hs' : s.re < 0 := hs
  have hre : 1 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hn : ∀ n : ℕ, (1 : ℂ) - s ≠ -(n : ℂ) := by
    intro n hcon
    have h : (1 - s).re = -(n : ℝ) := by rw [hcon]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [h] at hre
    linarith
  have h1 : (1 : ℂ) - s ≠ 1 := by
    intro hcon
    rw [hcon] at hre
    simp at hre
  have hz : riemannZeta ((1 : ℂ) - s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
    rw [cos_pi_one_sub_div_two]
    exact hsin
  have hfeq := hfe (1 - s) hn h1 hz hcos
  rw [show (1 : ℂ) - (1 - s) = s by ring] at hfeq
  rw [Gfun, Atilde, hfeq, tan_pi_one_sub_div_two]
  have hne0 : (1 : ℂ) - s ≠ 0 := by
    intro hcon
    have h : (1 - s).re = 0 := by rw [hcon]; simp
    rw [h] at hre
    linarith
  have hne1 : s - 1 ≠ 0 := by
    intro hcon
    apply hne0
    linear_combination -hcon
  field_simp
  ring

/-! ### Re-routing `𝓒_<`: a vertical leg instead of a diagonal one

**Finishing §8.2 means performing the contour shift, and the shape of `𝓒_<` decides how hard that
is.** With the paper's `135°` leg the region between `𝓒_<` and the real half-line is a rectangle
with one corner cut off, and Cauchy's theorem has to be applied to a triangle as well. With a
*vertical* leg from `-1` to `-1+i` the region is **exactly the rectangle** `[-R,-1] × [0,1]`, which
is the one shape Mathlib's `integral_boundary_rect_eq_zero_of_differentiableOn` covers.

The paper's reason for `45°` does not apply here. It wants `x^s` to decay along the leg, and
`lem:adamant` is what makes `45°` the smallest angle where `cot` stays bounded. This route already
gives up the powers of `log x` that decay would buy, and on a vertical leg the `cot` bound is
*easier*, not harder: at `Re s = -1`,

  `cot(πs/2) = cot(-π/2 + iπv/2) = -i tanh(πv/2)`,

so `|cot| = |tanh| ≤ 1` outright. `lem:adamant` and the diagonal segments above stay in the file —
they are correct and the bound on the diagonal is of independent interest — but the contour used
from here on is the vertical one.
-/

/-- The vertical leg of `𝓒_<`, from `-1` (at `v = 0`) to `-1+i` (at `v = 1`); `ds = i dv`. -/
noncomputable def segV (v : ℝ) : ℂ := -1 + (v : ℂ) * Complex.I

/-- The horizontal tail of `𝓒_<`, from `-1+i` (at `u = 0`) to `-∞+i`; `ds = -du`. -/
noncomputable def segH (u : ℝ) : ℂ := ((-1 - u : ℝ) : ℂ) + Complex.I

theorem segV_re (v : ℝ) : (segV v).re = -1 := by simp [segV]

theorem segV_im (v : ℝ) : (segV v).im = v := by simp [segV]

theorem segH_re (u : ℝ) : (segH u).re = -1 - u := by simp [segH]

theorem segH_im (u : ℝ) : (segH u).im = 1 := by simp [segH]

/-- **`|cot(πs/2)| ≤ 1` on the vertical line `Re s = -1`.**

`|cot z|² = (cos²x + sinh²y)/(sin²x + sinh²y)` with `x = -π/2`, where `cos x = 0` and `sin²x = 1`,
so the quotient is `sinh²y/(1 + sinh²y)`. This is the vertical leg's replacement for
`lem:adamant`, and it is strictly easier. -/
theorem norm_cot_segV_le (v : ℝ) : ‖Complex.cot ((Real.pi : ℂ) * segV v / 2)‖ ≤ 1 := by
  have hre : ((Real.pi : ℂ) * segV v / 2).re = -(Real.pi / 2) := by
    simp [segV, Complex.div_re, Complex.mul_re, Complex.normSq_apply]
    ring
  have hc : Real.cos (((Real.pi : ℂ) * segV v / 2).re) = 0 := by
    rw [hre, Real.cos_neg, Real.cos_pi_div_two]
  have hs : Real.sin (((Real.pi : ℂ) * segV v / 2).re) = -1 := by
    rw [hre, Real.sin_neg, Real.sin_pi_div_two]
  set y : ℝ := ((Real.pi : ℂ) * segV v / 2).im with hy
  have hsinsq : Complex.normSq (Complex.sin ((Real.pi : ℂ) * segV v / 2))
      = 1 + Real.sinh y ^ 2 := by
    rw [normSq_sin, hs]
    ring
  have hcossq : Complex.normSq (Complex.cos ((Real.pi : ℂ) * segV v / 2)) = Real.sinh y ^ 2 := by
    rw [normSq_cos, hc]
    ring
  have hsin0 : Complex.sin ((Real.pi : ℂ) * segV v / 2) ≠ 0 := by
    intro hcon
    rw [hcon] at hsinsq
    simp at hsinsq
    nlinarith [sq_nonneg (Real.sinh y)]
  have hsq : ‖Complex.cot ((Real.pi : ℂ) * segV v / 2)‖ ^ 2 ≤ 1 := by
    rw [Complex.cot_eq_cos_div_sin, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm,
      hcossq, hsinsq, div_le_one (by positivity)]
    nlinarith [sq_nonneg (Real.sinh y)]
  nlinarith [norm_nonneg (Complex.cot ((Real.pi : ℂ) * segV v / 2))]

/-- `|cot(πs/2)| ≤ 1 + 2/π` on the horizontal tail, where `Im(πs/2) = π/2`. -/
theorem norm_cot_segH_le (u : ℝ) :
    ‖Complex.cot ((Real.pi : ℂ) * segH u / 2)‖ ≤ 1 + 2 / Real.pi := by
  have hpi := Real.pi_pos
  have him : ((Real.pi : ℂ) * segH u / 2).im = Real.pi / 2 := by
    simp [Complex.mul_im, segH_im, segH_re]
  have h := norm_cot_le_coth (z := (Real.pi : ℂ) * segH u / 2) (by rw [him]; positivity)
  rw [him] at h
  refine le_trans h ?_
  have hc := CH2Section7.coth_le_one_add_inv (y := Real.pi / 2) (by positivity)
  calc Real.cosh (Real.pi / 2) / Real.sinh (Real.pi / 2) ≤ 1 + 1 / (Real.pi / 2) := hc
    _ = 1 + 2 / Real.pi := by field_simp

theorem norm_segV_sub_one_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : ‖segV v - 1‖ ≤ 3 := by
  have h : segV v - 1 = -2 + (v : ℂ) * Complex.I := by rw [segV]; ring
  rw [h]
  calc ‖(-2 : ℂ) + (v : ℂ) * Complex.I‖ ≤ ‖(-2 : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ 3 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hv0]
        norm_num
        linarith

theorem norm_segH_sub_one_le {u : ℝ} (hu : 0 ≤ u) : ‖segH u - 1‖ ≤ 3 + u := by
  have h : segH u - 1 = ((-2 - u : ℝ) : ℂ) + Complex.I := by
    rw [segH]; push_cast; ring
  rw [h]
  calc ‖((-2 - u : ℝ) : ℂ) + Complex.I‖ ≤ ‖((-2 - u : ℝ) : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
    _ = (2 + u) + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
          abs_of_nonpos (by linarith : (-2 - u : ℝ) ≤ 0)]
        ring
    _ = 3 + u := by ring

/-- The `cot` part of the integral over the vertical leg; `ds = i dv`. -/
noncomputable def intV (Φ : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ v in (0:ℝ)..1, ((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * segV v / 2) * Φ (segV v)
    * (x : ℂ) ^ segV v * Complex.I

/-- The `cot` part of the integral over the horizontal tail; `ds = -du`. -/
noncomputable def intH (Φ : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ u in Set.Ioi (0:ℝ), -(((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * segH u / 2)
    * Φ (segH u) * (x : ℂ) ^ segH u)

/-- **The vertical leg's `cot` contribution**: at most `3π/(2x)`. -/
theorem norm_intV_le {Φ : ℂ → ℂ}
    (hΦ : ∀ v ∈ Set.Icc (0:ℝ) 1, ‖Φ (segV v)‖ ≤ ‖segV v - 1‖)
    {x : ℝ} (hx : 1 < x) :
    ‖intV Φ x‖ ≤ 4.72 / x := by
  have hpi := Real.pi_pos
  have hpi2 : Real.pi < 3.141593 := Real.pi_lt_d6
  have hx0 : (0 : ℝ) < x := by linarith
  have hbound : ∀ v ∈ Set.uIoc (0:ℝ) 1,
      ‖((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * segV v / 2) * Φ (segV v)
        * (x : ℂ) ^ segV v * Complex.I‖ ≤ 4.72 / x := by
    intro v hv
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hv0 : (0 : ℝ) ≤ v := le_of_lt hv.1
    have hv1 : v ≤ 1 := hv.2
    have hc := norm_cot_segV_le v
    have hf : ‖Φ (segV v)‖ ≤ 3 :=
      le_trans (hΦ v ⟨hv0, hv1⟩) (norm_segV_sub_one_le hv0 hv1)
    have hxs : ‖(x : ℂ) ^ segV v‖ = 1 / x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, segV_re]
      rw [show (1 : ℝ) / x = x ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; simp]
    have hpihalf : ‖((Real.pi : ℂ) / 2)‖ = Real.pi / 2 := by
      rw [show ((Real.pi : ℝ) : ℂ) / 2 = (((Real.pi / 2 : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, hpihalf, hxs]
    have hcn : (0 : ℝ) ≤ ‖Complex.cot ((Real.pi : ℂ) * segV v / 2)‖ := norm_nonneg _
    have hfn : (0 : ℝ) ≤ ‖Φ (segV v)‖ := norm_nonneg _
    have hA : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segV v / 2)‖ ≤ Real.pi / 2 * 1 :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have hB : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segV v / 2)‖ * ‖Φ (segV v)‖
        ≤ Real.pi / 2 * 1 * 3 := mul_le_mul hA hf hfn (by positivity)
    have hfinal : Real.pi / 2 * 1 * 3 * (1 / x) ≤ 4.72 / x := by
      rw [mul_one_div, div_le_div_iff₀ hx0 hx0]
      nlinarith
    calc Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segV v / 2)‖ * ‖Φ (segV v)‖ * (1 / x)
        ≤ Real.pi / 2 * 1 * 3 * (1 / x) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ 4.72 / x := hfinal
  have hkey := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := 4.72 / x) hbound
  rw [intV]
  simpa using hkey

/-- **The horizontal tail's `cot` contribution**: at most `7.72/(x(log x - 1/3))`. -/
theorem norm_intH_le {Φ : ℂ → ℂ}
    (hΦ : ∀ u ∈ Set.Ioi (0:ℝ), ‖Φ (segH u)‖ ≤ ‖segH u - 1‖)
    {x : ℝ} (hx : 15 ≤ x) :
    ‖intH Φ x‖ ≤ 7.72 / (x * (Real.log x - 1 / 3)) := by
  have hpi := Real.pi_pos
  have hpi2 : Real.pi < 3.141593 := Real.pi_lt_d6
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : (2 : ℝ) < Real.log x := by
    have h1 : Real.log 15 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h2' : (2 : ℝ) < Real.log 15 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h := Real.exp_one_lt_d9
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he]
      nlinarith [Real.exp_pos 1]
    linarith
  have ha : -(Real.log x - 1 / 3) < 0 := by linarith
  have hpt : ∀ u ∈ Set.Ioi (0:ℝ),
      ‖-(((Real.pi : ℂ) / 2) * Complex.cot ((Real.pi : ℂ) * segH u / 2) * Φ (segH u)
        * (x : ℂ) ^ segH u)‖ ≤ 7.72 / x * Real.exp (-(Real.log x - 1 / 3) * u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hc := norm_cot_segH_le u
    have hf : ‖Φ (segH u)‖ ≤ 3 + u :=
      le_trans (hΦ u hu) (norm_segH_sub_one_le hu0.le)
    have hxs : ‖(x : ℂ) ^ segH u‖ = 1 / x * Real.exp (-(Real.log x * u)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, segH_re, Real.rpow_def_of_pos hx0,
        show Real.log x * (-1 - u) = -Real.log x + -(Real.log x * u) by ring, Real.exp_add]
      have h2' : Real.exp (-Real.log x) = 1 / x := by
        rw [Real.exp_neg, Real.exp_log hx0, one_div]
      rw [h2']
    have hpihalf : ‖((Real.pi : ℂ) / 2)‖ = Real.pi / 2 := by
      rw [show ((Real.pi : ℝ) : ℂ) / 2 = (((Real.pi / 2 : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hexp : (3 : ℝ) + u ≤ 3 * Real.exp (u / 3) := by
      have := Real.add_one_le_exp (u / 3)
      linarith
    rw [norm_neg, norm_mul, norm_mul, norm_mul, hpihalf, hxs]
    have hcn : (0 : ℝ) ≤ ‖Complex.cot ((Real.pi : ℂ) * segH u / 2)‖ := norm_nonneg _
    have hfn : (0 : ℝ) ≤ ‖Φ (segH u)‖ := norm_nonneg _
    have hA : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segH u / 2)‖
        ≤ Real.pi / 2 * (1 + 2 / Real.pi) := mul_le_mul_of_nonneg_left hc (by positivity)
    have hB : Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segH u / 2)‖ * ‖Φ (segH u)‖
        ≤ Real.pi / 2 * (1 + 2 / Real.pi) * (3 * Real.exp (u / 3)) :=
      mul_le_mul hA (le_trans hf hexp) hfn (by positivity)
    have hpos : (0 : ℝ) ≤ 1 / x * Real.exp (-(Real.log x * u)) := by positivity
    have hcoef : Real.pi / 2 * (1 + 2 / Real.pi) * 3 ≤ 7.72 := by
      have heq : Real.pi / 2 * (1 + 2 / Real.pi) * 3 = 3 / 2 * Real.pi + 3 := by
        field_simp
      rw [heq]
      linarith
    have hcollapse : Real.pi / 2 * (1 + 2 / Real.pi) * (3 * Real.exp (u / 3))
        * (1 / x * Real.exp (-(Real.log x * u)))
        ≤ 7.72 / x * Real.exp (-(Real.log x - 1 / 3) * u) := by
      have hexpeq : Real.exp (u / 3) * Real.exp (-(Real.log x * u))
          = Real.exp (-(Real.log x - 1 / 3) * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hrw : Real.pi / 2 * (1 + 2 / Real.pi) * (3 * Real.exp (u / 3))
          * (1 / x * Real.exp (-(Real.log x * u)))
          = (Real.pi / 2 * (1 + 2 / Real.pi) * 3) / x
            * (Real.exp (u / 3) * Real.exp (-(Real.log x * u))) := by ring
      rw [hrw, hexpeq]
      have hE : (0 : ℝ) < Real.exp (-(Real.log x - 1 / 3) * u) := Real.exp_pos _
      have hdiv : Real.pi / 2 * (1 + 2 / Real.pi) * 3 / x ≤ 7.72 / x := by gcongr
      nlinarith [hdiv, hE]
    calc Real.pi / 2 * ‖Complex.cot ((Real.pi : ℂ) * segH u / 2)‖ * ‖Φ (segH u)‖
          * (1 / x * Real.exp (-(Real.log x * u)))
        ≤ Real.pi / 2 * (1 + 2 / Real.pi) * (3 * Real.exp (u / 3))
          * (1 / x * Real.exp (-(Real.log x * u))) :=
          mul_le_mul_of_nonneg_right hB hpos
      _ ≤ 7.72 / x * Real.exp (-(Real.log x - 1 / 3) * u) := hcollapse
  have hint : ‖intH Φ x‖ ≤ ∫ u in Set.Ioi (0:ℝ), 7.72 / x * Real.exp (-(Real.log x - 1/3) * u) := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u ↦ norm_nonneg _)
      ((integrableOn_exp_mul_Ioi ha 0).const_mul _) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpt u hu
  refine le_trans hint (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi ha 0]
  have hne : Real.log x - 1 / 3 ≠ 0 := by linarith
  field_simp
  norm_num

/-! ### The contour shift

The last step of §8.2. For a function holomorphic on `Re s < 0`, the integral along `𝓒_<` — up the
vertical leg and out along `Im s = 1` — equals the integral straight out along the real axis.

Cauchy on the rectangle `[-1-R, -1] × [0, 1]` says the four sides cancel; three of them are the two
paths, and the fourth is the left edge at `Re s = -1-R`, which vanishes as `R → ∞` because the
integrand carries `x^s`. Both improper integrals are then limits of their truncations.

**This is the step the `135°` leg would have made awkward**, and it is why the contour was
re-routed: with a diagonal the region is not a rectangle. -/

/-- **The shift.** `∫_{𝓒_<} F = ∫_{-1}^{-∞} F` for `F` holomorphic on the left half-plane, given
integrability on the two half-lines and the vanishing of the left edge. -/
theorem contour_shift {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re < 0})
    (hint1 : MeasureTheory.IntegrableOn (fun u : ℝ ↦ -F (segH u)) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn (fun u : ℝ ↦ -F (((-1 - u : ℝ) : ℂ))) (Set.Ioi 0))
    (hdecay : Filter.Tendsto
      (fun R : ℝ ↦ ∫ y in (0:ℝ)..1, F (((-1 - R : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (nhds 0)) :
    (∫ v in (0:ℝ)..1, F (segV v) * Complex.I) + (∫ u in Set.Ioi (0:ℝ), -F (segH u))
      = ∫ u in Set.Ioi (0:ℝ), -F (((-1 - u : ℝ) : ℂ)) := by
  -- the rectangle identity, for each `R`
  have hrect : ∀ R : ℝ, 0 < R →
      (∫ v in (0:ℝ)..1, F (segV v) * Complex.I) + (∫ u in (0:ℝ)..R, -F (segH u))
        = (∫ u in (0:ℝ)..R, -F (((-1 - u : ℝ) : ℂ)))
          + Complex.I • ∫ y in (0:ℝ)..1, F (((-1 - R : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    intro R hR
    set z : ℂ := ((-1 - R : ℝ) : ℂ) with hz
    set w : ℂ := (-1 : ℂ) + Complex.I with hw
    have hzre : z.re = -1 - R := by simp [hz]
    have hzim : z.im = 0 := by simp [hz]
    have hwre : w.re = -1 := by simp [hw]
    have hwim : w.im = 1 := by simp [hw]
    have hsub : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ {s : ℂ | s.re < 0} := by
      intro p hp
      have hre : p.re ∈ Set.uIcc z.re w.re := hp.1
      rw [hzre, hwre, Set.uIcc_of_le (by linarith)] at hre
      exact lt_of_le_of_lt hre.2 (by norm_num)
    have hkey := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w (hF.mono hsub)
    rw [hzre, hzim, hwre, hwim] at hkey
    -- rewrite the two horizontal integrals in the `u` parametrisation
    have hbot : (∫ x : ℝ in (-1 - R)..(-1), F ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))
        = ∫ u : ℝ in (0:ℝ)..R, F (((-1 - u : ℝ) : ℂ)) := by
      rw [show (∫ u : ℝ in (0:ℝ)..R, F (((-1 - u : ℝ) : ℂ)))
        = ∫ u : ℝ in (0:ℝ)..R, (fun t : ℝ ↦ F ((t : ℂ) + ((0:ℝ) : ℂ) * Complex.I)) (-1 - u) by
          refine intervalIntegral.integral_congr fun u _ ↦ ?_
          push_cast
          ring_nf]
      rw [intervalIntegral.integral_comp_sub_left
        (fun t : ℝ ↦ F ((t : ℂ) + ((0:ℝ) : ℂ) * Complex.I)) (-1 : ℝ)]
      norm_num
    have htop : (∫ x : ℝ in (-1 - R)..(-1), F ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I))
        = ∫ u : ℝ in (0:ℝ)..R, F (segH u) := by
      rw [show (∫ u : ℝ in (0:ℝ)..R, F (segH u))
        = ∫ u : ℝ in (0:ℝ)..R, (fun t : ℝ ↦ F ((t : ℂ) + ((1:ℝ) : ℂ) * Complex.I)) (-1 - u) by
          refine intervalIntegral.integral_congr fun u _ ↦ ?_
          rw [segH]
          push_cast
          ring_nf]
      rw [intervalIntegral.integral_comp_sub_left
        (fun t : ℝ ↦ F ((t : ℂ) + ((1:ℝ) : ℂ) * Complex.I)) (-1 : ℝ)]
      norm_num
    have hright : (Complex.I • ∫ y : ℝ in (0:ℝ)..1, F (((-1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        = ∫ v in (0:ℝ)..1, F (segV v) * Complex.I := by
      rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v _ ↦ ?_
      rw [segV]
      push_cast
      ring
    have hleft : (Complex.I • ∫ y : ℝ in (0:ℝ)..1, F (((-1 - R : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        = Complex.I • ∫ y in (0:ℝ)..1, F (((-1 - R : ℝ) : ℂ) + (y : ℂ) * Complex.I) := rfl
    rw [hbot, htop, hright] at hkey
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg]
    linear_combination hkey
  -- pass to the limit
  have hlim1 : Filter.Tendsto (fun R : ℝ ↦ ∫ u in (0:ℝ)..R, -F (segH u)) Filter.atTop
      (nhds (∫ u in Set.Ioi (0:ℝ), -F (segH u))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint1 Filter.tendsto_id
  have hlim2 : Filter.Tendsto (fun R : ℝ ↦ ∫ u in (0:ℝ)..R, -F (((-1 - u : ℝ) : ℂ)))
      Filter.atTop (nhds (∫ u in Set.Ioi (0:ℝ), -F (((-1 - u : ℝ) : ℂ)))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint2 Filter.tendsto_id
  have hlim3 : Filter.Tendsto
      (fun R : ℝ ↦ Complex.I • ∫ y in (0:ℝ)..1, F (((-1 - R : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
    simpa using hdecay.const_smul Complex.I
  have hL : Filter.Tendsto
      (fun R : ℝ ↦ (∫ v in (0:ℝ)..1, F (segV v) * Complex.I) + (∫ u in (0:ℝ)..R, -F (segH u)))
      Filter.atTop
      (nhds ((∫ v in (0:ℝ)..1, F (segV v) * Complex.I)
        + ∫ u in Set.Ioi (0:ℝ), -F (segH u))) := hlim1.const_add _
  have hR : Filter.Tendsto
      (fun R : ℝ ↦ (∫ u in (0:ℝ)..R, -F (((-1 - u : ℝ) : ℂ)))
        + Complex.I • ∫ y in (0:ℝ)..1, F (((-1 - R : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (nhds ((∫ u in Set.Ioi (0:ℝ), -F (((-1 - u : ℝ) : ℂ))) + 0)) := hlim2.add hlim3
  have heq : (fun R : ℝ ↦ (∫ v in (0:ℝ)..1, F (segV v) * Complex.I)
      + (∫ u in (0:ℝ)..R, -F (segH u)))
      =ᶠ[Filter.atTop] fun R : ℝ ↦ (∫ u in (0:ℝ)..R, -F (((-1 - u : ℝ) : ℂ)))
        + Complex.I • ∫ y in (0:ℝ)..1, F (((-1 - R : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R hR'
    exact hrect R hR'
  have := tendsto_nhds_unique (hL.congr' heq) hR
  simpa using this

/-! ### `G` off the real axis

The two side conditions of `contour_shift` — integrability on the half-lines, and the vanishing of
the left edge — need `G` bounded on the strip `Re s ≤ -1`, `0 ≤ Im s ≤ 1`, which is off the real
axis and so needs a *complex* digamma asymptotic.

**The unnamed constant does not matter here, and that is the point.** `GammaAsymptotics.v2` states
its conclusion as an `O`-statement with a constant it does not name, which is useless for an
explicit estimate — but the constant is needed only for an integrability hypothesis and a limit.
The final explicit bound comes from `norm_intHoriz_le`, on the real axis, where `DigammaReal`
supplies `|ψ - log| ≤ 1/x` with the constant equal to `1`. So the `O`-form suffices, and none of
`GammaAsymptotics.v2`'s solution has to be re-proved. -/

/-- **`‖G(s)‖ ≤ A + log(1 + ‖s‖)` on the strip**, for some `A`.

`A` is unnamed because the imported digamma asymptotic's constant is; see the section note for why
that costs nothing. -/
theorem exists_norm_Gfun_le (hgam : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two) :
    ∃ A : ℝ, ∀ s : ℂ, s.re ≤ -1 → |s.im| ≤ 1 →
      ‖Gfun s‖ ≤ A + Real.log (1 + ‖s‖) := by
  obtain ⟨C, hC⟩ := hgam 1
  refine ⟨0.57 + |C| / 2 + Real.pi + 1 / 2 + ‖Complex.log (2 * (Real.pi : ℂ))‖, ?_⟩
  intro s hre him
  have hw2 : (2 : ℝ) ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hwn : (2 : ℝ) ≤ ‖1 - s‖ := le_trans hw2 (Complex.re_le_norm _)
  have hwn0 : (0 : ℝ) < ‖1 - s‖ := by linarith
  have hwim : |(1 - s).im| ≤ 1 := by
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    exact him
  -- the four pieces
  have hz : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ 0.57 :=
    norm_logDeriv_zeta_le h2v hw2
  have hd : ‖Complex.digamma (1 - s) - Complex.log (1 - s)‖ ≤ |C| / 2 := by
    refine le_trans (hC (1 - s) (by linarith) hwim) ?_
    have h1 : C / ‖1 - s‖ ≤ |C| / ‖1 - s‖ := by
      gcongr
      exact le_abs_self C
    refine le_trans h1 ?_
    rw [div_le_div_iff₀ hwn0 (by norm_num)]
    nlinarith [abs_nonneg C]
  have hlog : ‖Complex.log (1 - s)‖ ≤ Real.log (1 + ‖s‖) + Real.pi := by
    have h1 : ‖Complex.log (1 - s)‖
        ≤ |(Complex.log (1 - s)).re| + |(Complex.log (1 - s)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.log_re, Complex.log_im] at h1
    have h2 : |Real.log ‖1 - s‖| = Real.log ‖1 - s‖ :=
      abs_of_nonneg (Real.log_nonneg (by linarith))
    have h3 : |Complex.arg (1 - s)| ≤ Real.pi := Complex.abs_arg_le_pi _
    have h4 : ‖1 - s‖ ≤ 1 + ‖s‖ := by
      calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by simp
    have h5 : Real.log ‖1 - s‖ ≤ Real.log (1 + ‖s‖) := Real.log_le_log hwn0 h4
    linarith
  have hinv : ‖(1 : ℂ) / (1 - s)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    rw [div_le_div_iff₀ hwn0 (by norm_num)]
    linarith
  -- and the triangle inequality
  have hsplit : Gfun s = deriv riemannZeta (1 - s) / riemannZeta (1 - s)
      + (Complex.digamma (1 - s) - Complex.log (1 - s)) + Complex.log (1 - s)
      + 1 / (1 - s) - Complex.log (2 * (Real.pi : ℂ)) := by
    rw [Gfun]; ring
  rw [hsplit]
  calc ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)
        + (Complex.digamma (1 - s) - Complex.log (1 - s)) + Complex.log (1 - s)
        + 1 / (1 - s) - Complex.log (2 * (Real.pi : ℂ))‖
      ≤ ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)
          + (Complex.digamma (1 - s) - Complex.log (1 - s)) + Complex.log (1 - s)
          + 1 / (1 - s)‖ + ‖Complex.log (2 * (Real.pi : ℂ))‖ := norm_sub_le _ _
    _ ≤ ((‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)
          + (Complex.digamma (1 - s) - Complex.log (1 - s))‖ + ‖Complex.log (1 - s)‖)
          + ‖(1 : ℂ) / (1 - s)‖) + ‖Complex.log (2 * (Real.pi : ℂ))‖ := by
        gcongr
        exact le_trans (norm_add_le _ _) (by gcongr; exact norm_add_le _ _)
    _ ≤ ((‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
          + ‖Complex.digamma (1 - s) - Complex.log (1 - s)‖ + ‖Complex.log (1 - s)‖)
          + ‖(1 : ℂ) / (1 - s)‖) + ‖Complex.log (2 * (Real.pi : ℂ))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 0.57 + |C| / 2 + Real.pi + 1 / 2 + ‖Complex.log (2 * (Real.pi : ℂ))‖
        + Real.log (1 + ‖s‖) := by linarith

end CH2Section8
