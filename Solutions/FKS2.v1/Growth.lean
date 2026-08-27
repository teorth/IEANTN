/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Growth and monotonicity

The self-contained analytic toolkit FKS2's conversions rest on: when

`g a b c x = x^(-a) (log x)^b exp (c √(log x))`

is decreasing. Everything downstream is an application of this plus bookkeeping.

Nothing here mentions primes, so this is the cheapest part of the port and the right place to
start. It corresponds to the paper's Lemma 10 and Corollary 11.

## An erratum in the paper

The paper states its Lemma 10(c) with the inequality the wrong way round —
`√(log x) > -2b/c` where the argument gives `<`. `PrimeNumberTheoremAnd` noticed this and its
`lemma_10c` carries a note saying so; `g_strictAntiOn_of_a_zero` below states the corrected form.
Nothing in this port depends on the `a = 0` case, so the erratum costs nothing here, but it is
recorded because a reader comparing against the paper will otherwise think the transcription is
wrong.

## Provenance

The statements and proof strategies follow `PrimeNumberTheoremAnd`'s FKS2 development, whose
`lemma_10a`/`b`/`c` and `corollary_11` are the same results. Naming and structure are this
repository's.
-/

namespace FKS2Sol

open Real

/-- `g a b c x = x^(-a) (log x)^b exp (c √(log x))`, the shape every admissible bound in FKS2
reduces to once `log x / R` is unwound. -/
noncomputable def g (a b c x : ℝ) : ℝ :=
  x ^ (-a) * (log x) ^ b * exp (c * sqrt (log x))

/-- The derivative of `g`, which every monotonicity claim below reads off.

`d/dx g = (-a log x + b + (c/2)√(log x)) · x^{-a-1} (log x)^{b-1} exp(c √(log x))`. -/
theorem deriv_g {a b c x : ℝ} (hx : 1 < x) :
    deriv (g a b c) x =
      (-a * log x + b + (c / 2) * sqrt (log x)) * x ^ (-a - 1) * (log x) ^ (b - 1) *
        exp (c * sqrt (log x)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < log x := log_pos hx
  have hL : HasDerivAt log (1 / x) x := by simpa using Real.hasDerivAt_log hx0.ne'
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-a)) (-a * x ^ (-a - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
  have h2 : HasDerivAt (fun y : ℝ => (log y) ^ b) (b * (log x) ^ (b - 1) * (1 / x)) x :=
    (hL.rpow_const (Or.inl hlog.ne')).congr_deriv (by ring)
  have h3 : HasDerivAt (fun y : ℝ => sqrt (log y)) (1 / (2 * sqrt (log x)) * (1 / x)) x :=
    (hasDerivAt_sqrt hlog.ne').comp x hL
  have h4 : HasDerivAt (fun y : ℝ => exp (c * sqrt (log y)))
      (exp (c * sqrt (log x)) * (c * (1 / (2 * sqrt (log x)) * (1 / x)))) x :=
    (Real.hasDerivAt_exp _).comp x (h3.const_mul c)
  have hg : HasDerivAt (g a b c)
      ((-a * x ^ (-a - 1) * (log x) ^ b + x ^ (-a) * (b * (log x) ^ (b - 1) * (1 / x))) *
          exp (c * sqrt (log x))
        + x ^ (-a) * (log x) ^ b *
            (exp (c * sqrt (log x)) * (c * (1 / (2 * sqrt (log x)) * (1 / x))))) x := by
    unfold g
    exact (h1.mul h2).mul h4
  rw [hg.deriv]
  have hs : sqrt (log x) ≠ 0 := (sqrt_pos.mpr hlog).ne'
  have e1 : x ^ (-a) = x * x ^ (-a - 1) := by
    rw [show (-a : ℝ) = 1 + (-a - 1) by ring, rpow_add hx0]; simp
  have e2 : (log x) ^ b = log x * (log x) ^ (b - 1) := by
    rw [show (b : ℝ) = 1 + (b - 1) by ring, rpow_add hlog]; simp
  rw [e1, e2]
  -- Peeling one factor off each power leaves `x ^ (-a-1) * (log x) ^ (b-1) * exp …` times a
  -- bracket on both sides. Make those two powers opaque before touching `log x`: rewriting
  -- `log x = √(log x) * √(log x)` otherwise fires inside `(log x) ^ (b - 1)` and inside
  -- `√(log x)` itself, and the powers stop matching.
  set P := x ^ (-a - 1) with hP
  set Q := (log x) ^ (b - 1) with hQ
  set t := sqrt (log x) with ht
  have htt : t * t = log x := mul_self_sqrt hlog.le
  rw [← htt]
  field_simp

/-- `g` is continuous above `1`. Extracted because all three cases of Lemma 10 need it, and it
is the hypothesis `strictAntiOn_of_deriv_neg` wants on the closure. -/
theorem continuousAt_g {a b c : ℝ} {x : ℝ} (hx : 1 < x) : ContinuousAt (g a b c) x := by
  have hx0 : (0 : ℝ) < x := by linarith
  unfold g
  exact ((continuousAt_id.rpow continuousAt_const (Or.inl hx0.ne')).mul
    ((continuousAt_log hx0.ne').rpow continuousAt_const (Or.inl (log_pos hx).ne'))).mul
    (continuous_exp.continuousAt.comp (continuousAt_const.mul
      (continuous_sqrt.continuousAt.comp (continuousAt_log hx0.ne'))))

/-- `g` is decreasing exactly where a quadratic in `√(log x)` is negative.

Everything after this is about that quadratic, which is why the three cases below are the three
cases of a quadratic having no roots, having roots, or degenerating. -/
theorem deriv_g_neg_iff {a b c x : ℝ} (hx : 1 < x) :
    deriv (g a b c) x < 0 ↔ -a * sqrt (log x) ^ 2 + (c / 2) * sqrt (log x) + b < 0 := by
  have hlog := log_pos hx
  rw [deriv_g hx, sq_sqrt hlog.le]
  have hpos : 0 < x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) := by
    have : (0 : ℝ) < x := by linarith
    positivity
  rw [show ∀ y : ℝ, y * x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) =
      y * (x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x))) from fun _ ↦ by ring,
    mul_neg_iff]
  constructor <;> intro h
  · rcases h with ⟨-, hneg⟩ | ⟨h, -⟩ <;> linarith
  · exact Or.inr ⟨by linarith, hpos⟩

/-- **Lemma 10(a).** With `a > 0` and `b` strictly below the critical exponent `-c²/(16a)`, the
quadratic has no real root and `g` decreases on the whole of `(1, ∞)`.

This is the case the conversions actually use, through `admissibleBound_strictAntiOn`. -/
theorem g_strictAntiOn_of_lt {a b c : ℝ} (ha : 0 < a) (hb : b < -c ^ 2 / (16 * a)) :
    StrictAntiOn (g a b c) (Set.Ioi 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 1) (fun x hx ↦ (continuousAt_g hx.out).continuousWithinAt)
    (fun x hx ↦ ?_)
  · rw [interior_Ioi] at hx
    rw [deriv_g_neg_iff hx]
    -- complete the square: the quadratic in `√(log x)` has no root when `b + c²/(16a) < 0`
    set t := sqrt (log x) with ht
    have hsq : -a * t ^ 2 + (c / 2) * t + b
        = -a * (t - c / (4 * a)) ^ 2 + (b + c ^ 2 / (16 * a)) := by
      field_simp
      ring
    have hneg : b + c ^ 2 / (16 * a) < 0 := by
      have : -c ^ 2 / (16 * a) = -(c ^ 2 / (16 * a)) := by ring
      linarith [hb, this ▸ hb]
    rw [hsq]
    nlinarith [mul_nonneg ha.le (sq_nonneg (t - c / (4 * a)))]

/-- **Lemma 10(b).** At or above the critical exponent the quadratic does have roots, and `g`
decreases only beyond the larger one.

The threshold is explicit and that matters: it is where FKS2's `x₀`s come from, and a weaker
existential statement would lose the very thing the paper needs. -/
theorem g_strictAntiOn_of_ge {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hb : -c ^ 2 / (16 * a) ≤ b) :
    StrictAntiOn (g a b c)
      (Set.Ioi (exp ((c / (4 * a) + (1 / (2 * a)) * sqrt (c ^ 2 / 4 + 4 * a * b)) ^ 2))) := by
  -- `hb` says exactly that the discriminant is nonnegative, so the larger root `tPlus` is real.
  have hD : 0 ≤ c ^ 2 / 4 + 4 * a * b := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 16 * a)] at hb
    nlinarith
  set s := sqrt (c ^ 2 / 4 + 4 * a * b) with hs
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hs2 : s ^ 2 = c ^ 2 / 4 + 4 * a * b := sq_sqrt hD
  set tPlus := c / (4 * a) + (1 / (2 * a)) * s with htPlus
  have htPluspos : 0 < tPlus := by positivity
  -- `tPlus` really is a root: this is what turns `t > tPlus` into the sign of the quadratic.
  have hroot : a * tPlus ^ 2 - (c / 2) * tPlus - b = 0 := by
    rw [htPlus]; field_simp; nlinarith [hs2]
  have h1 : (1 : ℝ) < exp (tPlus ^ 2) := by
    rw [show (1 : ℝ) = exp 0 from (exp_zero).symm]
    exact exp_lt_exp.mpr (by positivity)
  refine strictAntiOn_of_deriv_neg (convex_Ioi _)
    (fun x hx ↦ (continuousAt_g (h1.trans hx.out)).continuousWithinAt) (fun x hx ↦ ?_)
  rw [interior_Ioi] at hx
  have hx1 : 1 < x := h1.trans hx
  rw [deriv_g_neg_iff hx1]
  -- `x > exp (tPlus²)` gives `√(log x) > tPlus`, and beyond the larger root the quadratic is negative.
  have hlogx : tPlus ^ 2 < log x := by
    rw [← log_exp (tPlus ^ 2)]; exact log_lt_log (exp_pos _) hx
  have ht : tPlus < sqrt (log x) := by
    rw [show tPlus = sqrt (tPlus ^ 2) from (sqrt_sq htPluspos.le).symm]
    exact sqrt_lt_sqrt (sq_nonneg _) hlogx
  set t := sqrt (log x) with htdef
  -- `a t² - (c/2) t - b = (t - tPlus)(a(t + tPlus) - c/2)`, and both factors are positive:
  -- `t > tPlus` for the first, and `t + tPlus > 2 tPlus ≥ c/(2a)` for the second.
  have hfac : c / 2 < a * (t + tPlus) := by
    have : c / (4 * a) ≤ tPlus := by
      rw [htPlus]
      have : 0 ≤ 1 / (2 * a) * s := by positivity
      linarith
    have h4a : (0 : ℝ) < 4 * a := by linarith
    rw [div_le_iff₀ h4a] at this
    nlinarith
  nlinarith [hroot, mul_pos (sub_pos.mpr ht) (sub_pos.mpr hfac)]

/-- **Lemma 10(c), corrected.** With `a = 0` and `b < 0`, `g` decreases on `(1, exp((-2b/c)²))`.

The paper writes this window's condition as `√(log x) > -2b/c`; the argument gives `<`, and the
statement here is the corrected one. See the module docstring. -/
theorem g_strictAntiOn_of_a_zero {b c : ℝ} (hb : b < 0) (hc : 0 < c) :
    StrictAntiOn (g 0 b c) (Set.Ioo 1 (exp ((-2 * b / c) ^ 2))) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hu : 0 < -2 * b / c := div_pos (by linarith) hc
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun x hx ↦ (continuousAt_g hx.1).continuousWithinAt) (fun x hx ↦ ?_)
  rw [interior_Ioo] at hx
  rw [deriv_g_neg_iff hx.1]
  -- With `a = 0` the quadratic degenerates to the line `(c/2) t + b`, negative exactly for
  -- `t < -2b/c` — the corrected direction; the paper prints `>`.
  have hlogx : log x < (-2 * b / c) ^ 2 := by
    rw [← log_exp ((-2 * b / c) ^ 2)]
    exact log_lt_log (by linarith [hx.1]) hx.2
  have ht : sqrt (log x) < -2 * b / c := by
    have h := sqrt_lt_sqrt (log_nonneg hx.1.le) hlogx
    rwa [sqrt_sq hu.le] at h
  have hkey : c / 2 * sqrt (log x) < -b := by
    have h := mul_lt_mul_of_pos_left ht (by linarith : (0 : ℝ) < c / 2)
    rwa [show c / 2 * (-2 * b / c) = -b by field_simp] at h
  linarith

/-- Lemma 10(a) and 10(b) combined: for `b ≤ -c²/(16a)`, `g` decreases beyond `exp((c/(4a))²)`.

The two cases of Lemma 10 meet exactly here. When the inequality is strict the discriminant
`c²/4 + 4ab` is negative, 10(a) applies and `g` decreases everywhere; at equality the discriminant
vanishes, 10(b) applies and its threshold is `exp((c/(4a))²)`. Either way that threshold works,
because `Real.sqrt` of a nonpositive number is `0`, so the two thresholds coincide. -/
theorem g_strictAntiOn_of_le {a b c X : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hb : b ≤ -c ^ 2 / (16 * a)) (h1 : 1 < X) (hX : exp ((c / (4 * a)) ^ 2) ≤ X) :
    StrictAntiOn (g a b c) (Set.Ioi X) := by
  have hdisc : c ^ 2 / 4 + 4 * a * b ≤ 0 := by
    rw [neg_div, le_neg, div_le_iff₀ (by positivity : (0 : ℝ) < 16 * a)] at hb
    linarith
  have hsqrt : sqrt (c ^ 2 / 4 + 4 * a * b) = 0 := sqrt_eq_zero_of_nonpos hdisc
  rcases eq_or_lt_of_le hb with heq | hlt
  · have hge := g_strictAntiOn_of_ge ha hc (le_of_eq heq.symm)
    rw [hsqrt] at hge
    refine hge.mono fun y hy ↦ ?_
    have : exp ((c / (4 * a) + 1 / (2 * a) * 0) ^ 2) ≤ X := by simpa using hX
    exact Set.mem_Ioi.mpr (lt_of_le_of_lt this hy)
  · exact (g_strictAntiOn_of_lt ha hlt).mono fun y hy ↦
      Set.mem_Ioi.mpr (lt_trans h1 hy)

/-- **Corollary 11.** For `B > 1 + C²/(16R)`, the function `g 1 (1 - B) (C/√R)` decreases on
`(1, ∞)`.

This is the form the conversions use: an admissible bound with parameters `B`, `C`, `R`, once
established at some `x₀`, keeps falling, so a bound proved at one point extends to everything
beyond it. It is Lemma 10(a) at `a = 1`, `b = 1 - B`, `c = C/√R`. -/
theorem admissibleBound_strictAntiOn {B C R : ℝ} (hR : 0 < R) (hB : 1 + C ^ 2 / (16 * R) < B) :
    StrictAntiOn (g 1 (1 - B) (C / sqrt R)) (Set.Ioi 1) := by
  apply g_strictAntiOn_of_lt one_pos
  rw [div_pow, sq_sqrt hR.le, mul_one]
  have : C ^ 2 / R / 16 = C ^ 2 / (16 * R) := by ring
  linarith

end FKS2Sol
