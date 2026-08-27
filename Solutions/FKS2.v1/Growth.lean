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
  -- What remains is algebra, not analysis. Peeling one factor off each power,
  --   `x ^ (-a) = x * x ^ (-a - 1)` and `(log x) ^ b = log x * (log x) ^ (b - 1)`,
  -- makes both sides `x ^ (-a-1) * (log x) ^ (b-1) * exp (…)` times a bracket, and the brackets
  -- agree once `log x / √(log x)` is rewritten as `√(log x)`. `field_simp; ring` does not close
  -- it as written: rewriting `log x = √(log x) ^ 2` fires inside `(log x) ^ (b - 1)` and inside
  -- `√(log x)` itself, so the powers stop matching. Generalising `(log x) ^ (b - 1)` and
  -- `x ^ (-a - 1)` to opaque variables first is the way through.
  sorry

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
  refine strictAntiOn_of_deriv_neg (convex_Ioi 1) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hx0 : (0 : ℝ) < x := by linarith [hx.out]
    exact (((continuousAt_id.rpow continuousAt_const (Or.inl hx0.ne')).mul
      ((continuousAt_log hx0.ne').rpow continuousAt_const
        (Or.inl (log_pos hx.out).ne'))).mul
      (continuous_exp.continuousAt.comp (continuousAt_const.mul
        (continuous_sqrt.continuousAt.comp (continuousAt_log hx0.ne'))))).continuousWithinAt
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
  sorry

/-- **Lemma 10(c), corrected.** With `a = 0` and `b < 0`, `g` decreases on `(1, exp((-2b/c)²))`.

The paper writes this window's condition as `√(log x) > -2b/c`; the argument gives `<`, and the
statement here is the corrected one. See the module docstring. -/
theorem g_strictAntiOn_of_a_zero {b c : ℝ} (hb : b < 0) (hc : 0 < c) :
    StrictAntiOn (g 0 b c) (Set.Ioo 1 (exp ((-2 * b / c) ^ 2))) := by
  sorry

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
