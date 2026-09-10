/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 8.1: the integral on the real line

§8.1 of Chirre–Helfgott bounds `∫_{-1/2}^{1} |ζ'/ζ(σ+it)| (1-σ) x^{-(1-σ)} dσ` for a well-chosen
`t`. Its output is `cor:adiaro`, which `lem:hardin` turns into the horizontal contribution.

This file begins at the bottom of the chain, with the two pieces that depend on nothing at all:
`lem:bettnist`, a bound on the exponential integral, and `lem:rameau`, the integral estimate that
`lem:saghar` applies once per zero.

## No `Ei`, no `γ`, and no numerics

The paper states `lem:bettnist` as `Ei(X) ≤ (e^X/X)(1 + 1/X + 2/X² + (40/3)/X³)`, proved by showing
that `f - Ei` has a single critical point, at `X = 80/11`, and checking it there with Arb. The
margin is `0.0034` out of `239.65` — a relative `1.4 × 10⁻⁵`, which would need seven digits of both
`Ei(80/11)` and `γ`, and Mathlib has only `1/2 < γ < 2/3`.

**There is a factor of 4.7 of room in that constant**, traced back from §9: the coefficient of
`1/log⁴x` in `eq:arguc2` may be as large as `498` where the paper's is `320/3`. With `40/3` replaced
by `40` the bound becomes elementary. Substituting `w = X - v`,

`∫₁^X e^w/w dw = e^X ∫₀^{X-1} e^{-v}/(X-v) dv`,

and on that range `X - v ≥ 1`, so expanding

`1/(X-v) = 1/X + v/X² + v²/X³ + v³/X⁴ + v⁴/(X⁴(X-v))`

and using `∫₀^{X-1} v^k e^{-v} dv ≤ k!` five times gives
`∫₁^X e^w/w dw ≤ e^X (1/X + 1/X² + 2/X³ + 30/X⁴)`. No critical point, no quadrature.

`γ` disappears the same way. Working with `EiAux X = ∫₀^X (e^w - 1)/w dw`, which is `Ei - log X - γ`,
the `γ` and `log X` of the paper's `eq:arguc1` sit only in terms of size `1/√x` — `3 × 10⁻⁵` at
`x ≥ 10⁹`, against a `2/log²x = 0.0047` that has to be exact — where the `arsinh` slack absorbs them.
-/

namespace CH2Section81

open scoped Nat

/-! ### `∫₀^Y vᵏ e^{-v} dv ≤ k!`

Five instances of one antiderivative: if `Q - Q' = vᵏ` then `-e^{-v} Q(v)` differentiates to
`vᵏ e^{-v}`, and `Q(0) = k!` with `Q ≥ 0` on `[0,∞)`. -/

theorem integral_pow_exp_le {Y : ℝ} (hY : 0 ≤ Y) {k : ℕ} {c : ℝ} {Q Q' : ℝ → ℝ}
    (hd : ∀ v : ℝ, HasDerivAt Q (Q' v) v)
    (hQ : ∀ v : ℝ, Q v - Q' v = v ^ k)
    (hQ0 : Q 0 = c) (hQnn : ∀ v : ℝ, 0 ≤ v → 0 ≤ Q v) :
    ∫ v in (0:ℝ)..Y, v ^ k * Real.exp (-v) ≤ c := by
  have hderiv : ∀ v ∈ Set.uIcc (0:ℝ) Y,
      HasDerivAt (fun w : ℝ ↦ -(Real.exp (-w) * Q w)) (v ^ k * Real.exp (-v)) v := by
    intro v _
    have hn : HasDerivAt (fun w : ℝ ↦ -w) (-1 : ℝ) v := hasDerivAt_neg' v
    have he : HasDerivAt (fun w : ℝ ↦ Real.exp (-w)) (-Real.exp (-v)) v := by
      have h := (Real.hasDerivAt_exp (-v)).comp v hn
      rw [Function.comp_def] at h
      exact h.congr_deriv (by ring)
    have hmul := (he.mul (hd v)).neg
    have hval : -(-Real.exp (-v) * Q v + Real.exp (-v) * Q' v) = v ^ k * Real.exp (-v) := by
      rw [← hQ v]; ring
    rw [hval] at hmul
    exact hmul
  have hint : IntervalIntegrable (fun v : ℝ ↦ v ^ k * Real.exp (-v)) MeasureTheory.volume 0 Y :=
    (((continuous_pow k).mul (Real.continuous_exp.comp continuous_neg))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : (0:ℝ) ≤ Real.exp (-Y) * Q Y := mul_nonneg (Real.exp_pos _).le (hQnn Y hY)
  simp only [neg_zero, Real.exp_zero, one_mul, hQ0]
  linarith

theorem integral_exp_le {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ v in (0:ℝ)..Y, v ^ 0 * Real.exp (-v) ≤ 1 := by
  refine integral_pow_exp_le hY (Q := fun _ ↦ (1:ℝ)) (Q' := fun _ ↦ 0)
    (fun v ↦ hasDerivAt_const v 1) (fun v ↦ by norm_num) rfl (fun v _ ↦ by norm_num)

/-- `d/dv (c vⁿ⁺¹) = c (n+1) vⁿ`, in the shape the four instances below need. -/
theorem hasDerivAt_monomial (n : ℕ) (c : ℝ) (v : ℝ) :
    HasDerivAt (fun w : ℝ ↦ c * w ^ (n + 1)) (c * (n + 1) * v ^ n) v := by
  have h := (hasDerivAt_pow (n + 1) v).const_mul c
  refine h.congr_deriv ?_
  push_cast
  ring

theorem integral_id_exp_le {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ v in (0:ℝ)..Y, v ^ 1 * Real.exp (-v) ≤ 1 := by
  refine integral_pow_exp_le hY (Q := fun v ↦ v + 1) (Q' := fun _ ↦ 1)
    (fun v ↦ ?_) (fun v ↦ by ring) (by norm_num) (fun v hv ↦ by linarith)
  simpa using (hasDerivAt_id v).add_const 1

theorem integral_sq_exp_le {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ v in (0:ℝ)..Y, v ^ 2 * Real.exp (-v) ≤ 2 := by
  refine integral_pow_exp_le hY (Q := fun v ↦ v ^ 2 + 2 * v + 2) (Q' := fun v ↦ 2 * v + 2)
    (fun v ↦ ?_) (fun v ↦ by ring) (by norm_num) (fun v hv ↦ by positivity)
  have h1 : HasDerivAt (fun w : ℝ ↦ (1:ℝ) * w ^ 2) (1 * ((1:ℕ) + 1) * v ^ 1) v :=
    hasDerivAt_monomial 1 1 v
  have h2 : HasDerivAt (fun w : ℝ ↦ (2:ℝ) * w ^ 1) (2 * ((0:ℕ) + 1) * v ^ 0) v :=
    hasDerivAt_monomial 0 2 v
  have h3 := (h1.add h2).add_const 2
  have h4 : HasDerivAt (fun v : ℝ ↦ v ^ 2 + 2 * v + 2)
      (1 * ((1:ℕ) + 1) * v ^ 1 + 2 * ((0:ℕ) + 1) * v ^ 0) v := by
    simpa using h3
  exact h4.congr_deriv (by push_cast; ring)

theorem integral_cube_exp_le {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ v in (0:ℝ)..Y, v ^ 3 * Real.exp (-v) ≤ 6 := by
  refine integral_pow_exp_le hY (Q := fun v ↦ v ^ 3 + 3 * v ^ 2 + 6 * v + 6)
    (Q' := fun v ↦ 3 * v ^ 2 + 6 * v + 6) (fun v ↦ ?_) (fun v ↦ by ring) (by norm_num)
    (fun v hv ↦ by positivity)
  have h1 : HasDerivAt (fun w : ℝ ↦ (1:ℝ) * w ^ 3) (1 * ((2:ℕ) + 1) * v ^ 2) v :=
    hasDerivAt_monomial 2 1 v
  have h2 : HasDerivAt (fun w : ℝ ↦ (3:ℝ) * w ^ 2) (3 * ((1:ℕ) + 1) * v ^ 1) v :=
    hasDerivAt_monomial 1 3 v
  have h3 : HasDerivAt (fun w : ℝ ↦ (6:ℝ) * w ^ 1) (6 * ((0:ℕ) + 1) * v ^ 0) v :=
    hasDerivAt_monomial 0 6 v
  have h4 := ((h1.add h2).add h3).add_const 6
  have h5 : HasDerivAt (fun v : ℝ ↦ v ^ 3 + 3 * v ^ 2 + 6 * v + 6)
      (1 * ((2:ℕ) + 1) * v ^ 2 + 3 * ((1:ℕ) + 1) * v ^ 1 + 6 * ((0:ℕ) + 1) * v ^ 0) v := by
    simpa using h4
  exact h5.congr_deriv (by push_cast; ring)

theorem integral_quart_exp_le {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ v in (0:ℝ)..Y, v ^ 4 * Real.exp (-v) ≤ 24 := by
  refine integral_pow_exp_le hY (Q := fun v ↦ v ^ 4 + 4 * v ^ 3 + 12 * v ^ 2 + 24 * v + 24)
    (Q' := fun v ↦ 4 * v ^ 3 + 12 * v ^ 2 + 24 * v + 24) (fun v ↦ ?_) (fun v ↦ by ring)
    (by norm_num) (fun v hv ↦ by positivity)
  have h1 : HasDerivAt (fun w : ℝ ↦ (1:ℝ) * w ^ 4) (1 * ((3:ℕ) + 1) * v ^ 3) v :=
    hasDerivAt_monomial 3 1 v
  have h2 : HasDerivAt (fun w : ℝ ↦ (4:ℝ) * w ^ 3) (4 * ((2:ℕ) + 1) * v ^ 2) v :=
    hasDerivAt_monomial 2 4 v
  have h3 : HasDerivAt (fun w : ℝ ↦ (12:ℝ) * w ^ 2) (12 * ((1:ℕ) + 1) * v ^ 1) v :=
    hasDerivAt_monomial 1 12 v
  have h4 : HasDerivAt (fun w : ℝ ↦ (24:ℝ) * w ^ 1) (24 * ((0:ℕ) + 1) * v ^ 0) v :=
    hasDerivAt_monomial 0 24 v
  have h5 := (((h1.add h2).add h3).add h4).add_const 24
  have h6 : HasDerivAt (fun v : ℝ ↦ v ^ 4 + 4 * v ^ 3 + 12 * v ^ 2 + 24 * v + 24)
      (1 * ((3:ℕ) + 1) * v ^ 3 + 4 * ((2:ℕ) + 1) * v ^ 2 + 12 * ((1:ℕ) + 1) * v ^ 1
        + 24 * ((0:ℕ) + 1) * v ^ 0) v := by
    simpa using h5
  exact h6.congr_deriv (by push_cast; ring)

/-- A non-negative quartic against `e^{-v}`, integrated: `∫₀^Y P(v) e^{-v} dv ≤ P` evaluated on the
factorials. -/
theorem integral_comb_le {Y : ℝ} (hY : 0 ≤ Y) {c0 c1 c2 c3 c4 : ℝ}
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) :
    (∫ v in (0:ℝ)..Y, (c0 * v ^ 0 + c1 * v ^ 1 + c2 * v ^ 2 + c3 * v ^ 3 + c4 * v ^ 4)
        * Real.exp (-v))
      ≤ c0 + c1 + 2 * c2 + 6 * c3 + 24 * c4 := by
  have hi : ∀ k : ℕ, ∀ c : ℝ, IntervalIntegrable (fun v : ℝ ↦ c * (v ^ k * Real.exp (-v)))
      MeasureTheory.volume 0 Y := fun k c ↦
    (continuous_const.mul ((continuous_pow k).mul
      (Real.continuous_exp.comp continuous_neg))).intervalIntegrable _ _
  have I0 := hi 0 c0
  have I1 := hi 1 c1
  have I2 := hi 2 c2
  have I3 := hi 3 c3
  have I4 := hi 4 c4
  have heq : ∀ v : ℝ,
      (c0 * v ^ 0 + c1 * v ^ 1 + c2 * v ^ 2 + c3 * v ^ 3 + c4 * v ^ 4) * Real.exp (-v)
        = c0 * (v ^ 0 * Real.exp (-v)) + c1 * (v ^ 1 * Real.exp (-v))
          + c2 * (v ^ 2 * Real.exp (-v)) + c3 * (v ^ 3 * Real.exp (-v))
          + c4 * (v ^ 4 * Real.exp (-v)) := by
    intro v; ring
  rw [intervalIntegral.integral_congr (g := fun v : ℝ ↦
      c0 * (v ^ 0 * Real.exp (-v)) + c1 * (v ^ 1 * Real.exp (-v))
        + c2 * (v ^ 2 * Real.exp (-v)) + c3 * (v ^ 3 * Real.exp (-v))
        + c4 * (v ^ 4 * Real.exp (-v))) (fun v _ ↦ heq v),
    intervalIntegral.integral_add (((I0.add I1).add I2).add I3) I4,
    intervalIntegral.integral_add ((I0.add I1).add I2) I3,
    intervalIntegral.integral_add (I0.add I1) I2,
    intervalIntegral.integral_add I0 I1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have b0 := mul_le_mul_of_nonneg_left (integral_exp_le hY) h0
  have b1 := mul_le_mul_of_nonneg_left (integral_id_exp_le hY) h1
  have b2 := mul_le_mul_of_nonneg_left (integral_sq_exp_le hY) h2
  have b3 := mul_le_mul_of_nonneg_left (integral_cube_exp_le hY) h3
  have b4 := mul_le_mul_of_nonneg_left (integral_quart_exp_le hY) h4
  linarith

/-! ### The exponential integral, `lem:bettnist`

`∫₁^X e^w/w dw ≤ e^X (1/X + 1/X² + 2/X³ + 30/X⁴)`, from the substitution `w = X - v` and one
geometric expansion. The `30` is `6 + 24`: the exact `3!` coefficient plus the crude `4!` bound on
the remainder, which is where the paper's `Ei` asymptotic gets its `6/X⁴` and we lose a factor. -/

theorem integral_exp_div_le {X : ℝ} (hX : 1 ≤ X) :
    (∫ w in (1:ℝ)..X, Real.exp w / w)
      ≤ Real.exp X * (1 / X + 1 / X ^ 2 + 2 / X ^ 3 + 30 / X ^ 4) := by
  have hX0 : (0:ℝ) < X := by linarith
  have hY : (0:ℝ) ≤ X - 1 := by linarith
  have hsub : (∫ v in (0:ℝ)..(X - 1), Real.exp (X - v) / (X - v))
      = ∫ w in (1:ℝ)..X, Real.exp w / w := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := X - 1)
      (fun w : ℝ ↦ Real.exp w / w) X
    simpa using h
  rw [← hsub]
  have hcont : ContinuousOn (fun v : ℝ ↦ Real.exp (X - v) / (X - v)) (Set.uIcc 0 (X - 1)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro v hv
    rw [Set.uIcc_of_le hY] at hv
    have : v ≤ X - 1 := hv.2
    intro hc
    linarith [sub_eq_zero.mp hc]
  have hint1 : IntervalIntegrable (fun v : ℝ ↦ Real.exp (X - v) / (X - v))
      MeasureTheory.volume 0 (X - 1) := hcont.intervalIntegrable
  have hint2 : IntervalIntegrable (fun v : ℝ ↦ Real.exp X *
      ((1 / X * v ^ 0 + 1 / X ^ 2 * v ^ 1 + 1 / X ^ 3 * v ^ 2 + 1 / X ^ 4 * v ^ 3
        + 1 / X ^ 4 * v ^ 4) * Real.exp (-v))) MeasureTheory.volume 0 (X - 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpt : ∀ v ∈ Set.Icc (0:ℝ) (X - 1), Real.exp (X - v) / (X - v)
      ≤ Real.exp X * ((1 / X * v ^ 0 + 1 / X ^ 2 * v ^ 1 + 1 / X ^ 3 * v ^ 2 + 1 / X ^ 4 * v ^ 3
        + 1 / X ^ 4 * v ^ 4) * Real.exp (-v)) := by
    intro v hv
    have hv0 : (0:ℝ) ≤ v := hv.1
    have hXv : (1:ℝ) ≤ X - v := by linarith [hv.2]
    have hXv0 : (0:ℝ) < X - v := by linarith
    have hid : 1 / (X - v)
        = 1 / X + v / X ^ 2 + v ^ 2 / X ^ 3 + v ^ 3 / X ^ 4 + v ^ 4 / (X ^ 4 * (X - v)) := by
      field_simp
      ring
    have htail : v ^ 4 / (X ^ 4 * (X - v)) ≤ v ^ 4 / X ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hv0 4) (pow_pos hX0 4).le)
        (sub_nonneg.mpr hXv)]
    have hinv : 1 / (X - v) ≤ 1 / X * v ^ 0 + 1 / X ^ 2 * v ^ 1 + 1 / X ^ 3 * v ^ 2
        + 1 / X ^ 4 * v ^ 3 + 1 / X ^ 4 * v ^ 4 := by
      have hrhs : 1 / X * v ^ 0 + 1 / X ^ 2 * v ^ 1 + 1 / X ^ 3 * v ^ 2
          + 1 / X ^ 4 * v ^ 3 + 1 / X ^ 4 * v ^ 4
          = 1 / X + v / X ^ 2 + v ^ 2 / X ^ 3 + v ^ 3 / X ^ 4 + v ^ 4 / X ^ 4 := by ring
      rw [hid, hrhs]
      linarith [htail]
    have hexp : Real.exp (X - v) = Real.exp X * Real.exp (-v) := by
      rw [← Real.exp_add]
      congr 1
    have hrw1 : Real.exp (X - v) / (X - v)
        = Real.exp X * Real.exp (-v) * (1 / (X - v)) := by
      rw [hexp]; ring
    have hrw2 : Real.exp X * ((1 / X * v ^ 0 + 1 / X ^ 2 * v ^ 1 + 1 / X ^ 3 * v ^ 2
          + 1 / X ^ 4 * v ^ 3 + 1 / X ^ 4 * v ^ 4) * Real.exp (-v))
        = Real.exp X * Real.exp (-v) * (1 / X * v ^ 0 + 1 / X ^ 2 * v ^ 1 + 1 / X ^ 3 * v ^ 2
          + 1 / X ^ 4 * v ^ 3 + 1 / X ^ 4 * v ^ 4) := by ring
    rw [hrw1, hrw2]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  refine le_trans (intervalIntegral.integral_mono_on hY hint1 hint2 hpt) ?_
  rw [intervalIntegral.integral_const_mul]
  have hb := integral_comb_le (Y := X - 1) hY (c0 := 1 / X) (c1 := 1 / X ^ 2) (c2 := 1 / X ^ 3)
    (c3 := 1 / X ^ 4) (c4 := 1 / X ^ 4) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity)
  have hE : (0:ℝ) < Real.exp X := Real.exp_pos X
  calc Real.exp X * ∫ v in (0:ℝ)..(X - 1), (1 / X * v ^ 0 + 1 / X ^ 2 * v ^ 1 + 1 / X ^ 3 * v ^ 2
        + 1 / X ^ 4 * v ^ 3 + 1 / X ^ 4 * v ^ 4) * Real.exp (-v)
      ≤ Real.exp X * (1 / X + 1 / X ^ 2 + 2 * (1 / X ^ 3) + 6 * (1 / X ^ 4)
          + 24 * (1 / X ^ 4)) := by
        exact mul_le_mul_of_nonneg_left hb hE.le
    _ = Real.exp X * (1 / X + 1 / X ^ 2 + 2 / X ^ 3 + 30 / X ^ 4) := by ring

/-- `X⁴ ≤ 6.5536 e^X` for `X ≥ 0`: four Taylor terms of `e^{X/4}`, raised to the fourth power.

The truth is `X⁴ e^{-X} ≤ 256/e⁴ = 4.689`, attained at `X = 4`; this route gives `6.5536 = 1.6⁴`
with no monotonicity argument, which is all the `Ei` bound needs. -/
theorem quartic_le_exp {X : ℝ} (hX : 0 ≤ X) : X ^ 4 ≤ 6.5536 * Real.exp X := by
  set A : ℝ := 1 + X / 4 + (X / 4) ^ 2 / 2 + (X / 4) ^ 3 / 6 with hA
  have hA0 : (0:ℝ) ≤ A := by rw [hA]; positivity
  have hTaylor : A ≤ Real.exp (X / 4) := by
    have h := Real.sum_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ X / 4) 4
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    rw [hA]
    linarith
  have hpow : A ^ 4 ≤ Real.exp X := by
    have h1 : A ^ 4 ≤ Real.exp (X / 4) ^ 4 := pow_le_pow_left₀ hA0 hTaylor 4
    have h2 : Real.exp (X / 4) ^ 4 = Real.exp X := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    linarith
  have hlin : X ≤ 1.6 * A := by
    rw [hA]
    nlinarith [mul_nonneg hX (sq_nonneg (X - 4)), sq_nonneg (X - 4), hX]
  have h4 : X ^ 4 ≤ (1.6 * A) ^ 4 := pow_le_pow_left₀ hX hlin 4
  have h5 : (1.6 * A) ^ 4 = 6.5536 * A ^ 4 := by ring
  nlinarith [hpow, hA0, pow_nonneg hA0 4]

/-- `EiAux X = ∫₀^X (e^w - 1)/w dw`, which is `Ei(X) - log X - γ`.

Defined this way so that neither `Ei` nor `γ` — of which Mathlib knows only `1/2 < γ < 2/3` — ever
appears. Note `(e^0 - 1)/0 = 0` is a junk value; it sits on a null set and does not matter, but it
is why the integrand is not continuous at `0` and integrability there needs the bound, not
`ContinuousOn`. -/
noncomputable def EiAux (X : ℝ) : ℝ := ∫ w in (0:ℝ)..X, (Real.exp w - 1) / w

/-- `(e^w - 1)/w ≤ e^w` for `w ≥ 0`, which is `1 - w ≤ e^{-w}`. -/
theorem sub_one_div_le_exp {w : ℝ} (hw : 0 ≤ w) : (Real.exp w - 1) / w ≤ Real.exp w := by
  rcases eq_or_lt_of_le hw with h | h
  · rw [← h]
    norm_num
  · rw [div_le_iff₀ h]
    have h1 := Real.add_one_le_exp (-w)
    have h2 : Real.exp w * (1 - w) ≤ Real.exp w * Real.exp (-w) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos w).le
    have h3 : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [h2, h3]

theorem intervalIntegrable_eiAux_zero_one :
    IntervalIntegrable (fun w : ℝ ↦ (Real.exp w - 1) / w) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ ↦ Real.exp 1) ?_ ?_ ?_
  · exact MeasureTheory.integrableOn_const (by simp) (by simp)
  · exact ((Real.measurable_exp.sub measurable_const).div measurable_id).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with w hw
    have hw0 : (0:ℝ) < w := hw.1
    have hw1 : w ≤ 1 := hw.2
    have hnn : (0:ℝ) ≤ (Real.exp w - 1) / w := by
      have : (1:ℝ) ≤ Real.exp w := Real.one_le_exp hw0.le
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact le_trans (sub_one_div_le_exp hw0.le) (Real.exp_le_exp.mpr hw1)

/-- **`lem:bettnist`**, in the `Ei`-free form: `EiAux X ≤ e^X (1/X + 1/X² + 2/X³ + 42/X⁴)`.

The paper has `40/3` where this has `42`, at the cost of a critical-point argument and seven digits
of `Ei(80/11)`; §9 tolerates anything up to `498/8 = 62`. See the module docstring. -/
theorem eiAux_le {X : ℝ} (hX : 1 ≤ X) :
    EiAux X ≤ Real.exp X * (1 / X + 1 / X ^ 2 + 2 / X ^ 3 + 42 / X ^ 4) := by
  have hX0 : (0:ℝ) < X := by linarith
  have hint01 := intervalIntegrable_eiAux_zero_one
  have hcont1X : ContinuousOn (fun w : ℝ ↦ (Real.exp w - 1) / w) (Set.uIcc 1 X) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro w hw
    rw [Set.uIcc_of_le hX] at hw
    have : (1:ℝ) ≤ w := hw.1
    linarith
  have hint1X : IntervalIntegrable (fun w : ℝ ↦ (Real.exp w - 1) / w)
      MeasureTheory.volume 1 X := hcont1X.intervalIntegrable
  have hsplit : EiAux X
      = (∫ w in (0:ℝ)..1, (Real.exp w - 1) / w) + ∫ w in (1:ℝ)..X, (Real.exp w - 1) / w :=
    (intervalIntegral.integral_add_adjacent_intervals hint01 hint1X).symm
  -- the piece near the singularity
  have hA : (∫ w in (0:ℝ)..1, (Real.exp w - 1) / w) ≤ Real.exp 1 - 1 := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hint01
      (Real.continuous_exp.intervalIntegrable _ _) (fun w hw ↦ sub_one_div_le_exp hw.1)
    have hval : (∫ w in (0:ℝ)..1, Real.exp w) = Real.exp 1 - 1 := by
      simp [integral_exp]
    linarith [hmono, hval.le, hval.ge]
  -- the tail
  have hcontE : ContinuousOn (fun w : ℝ ↦ Real.exp w / w) (Set.uIcc 1 X) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro w hw
    rw [Set.uIcc_of_le hX] at hw
    have : (1:ℝ) ≤ w := hw.1
    linarith
  have hB : (∫ w in (1:ℝ)..X, (Real.exp w - 1) / w) ≤ ∫ w in (1:ℝ)..X, Real.exp w / w := by
    refine intervalIntegral.integral_mono_on hX hint1X hcontE.intervalIntegrable ?_
    intro w hw
    have hw1 : (1:ℝ) ≤ w := hw.1
    have hw0 : (0:ℝ) < w := by linarith
    have hnum : Real.exp w - 1 ≤ Real.exp w := by linarith
    exact div_le_div_of_nonneg_right hnum hw0.le
  have hC := integral_exp_div_le hX
  -- and the arithmetic
  have hq := quartic_le_exp hX0.le
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hE : (0:ℝ) < Real.exp X := Real.exp_pos X
  have hX4 : (0:ℝ) < X ^ 4 := by positivity
  have hgap : Real.exp 1 - 1 ≤ Real.exp X * (12 / X ^ 4) := by
    have h1 : Real.exp X * (12 / X ^ 4) = 12 * Real.exp X / X ^ 4 := by ring
    rw [h1, le_div_iff₀ hX4]
    have hb : (Real.exp 1 - 1) * X ^ 4 ≤ 1.7182818286 * (6.5536 * Real.exp X) :=
      mul_le_mul (by linarith) hq hX4.le (by norm_num)
    nlinarith [hb, hE]
  have hrw : Real.exp X * (1 / X + 1 / X ^ 2 + 2 / X ^ 3 + 42 / X ^ 4)
      = Real.exp X * (1 / X + 1 / X ^ 2 + 2 / X ^ 3 + 30 / X ^ 4) + Real.exp X * (12 / X ^ 4) := by
    ring
  rw [hsplit, hrw]
  linarith [hA, hB, hC, hgap]

/-! ### The four closed forms `lem:rameau` needs

`arsinh` for the leading piece, `EiAux` for the singular one, and two elementary antiderivatives. -/

/-- `∫₀^b dv/√(η²+v²) = arsinh(b/η)`. -/
theorem integral_one_div_sqrt_sq_add_sq {η : ℝ} (hη : 0 < η) (b : ℝ) :
    (∫ v in (0:ℝ)..b, 1 / Real.sqrt (η ^ 2 + v ^ 2)) = Real.arsinh (b / η) := by
  have hderiv : ∀ v : ℝ, HasDerivAt (fun w : ℝ ↦ Real.arsinh (w / η))
      (1 / Real.sqrt (η ^ 2 + v ^ 2)) v := by
    intro v
    have hinner : HasDerivAt (fun w : ℝ ↦ w / η) (1 / η) v := by
      simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id v).div_const η
    have h := (Real.hasDerivAt_arsinh (v / η)).comp v hinner
    rw [Function.comp_def] at h
    refine h.congr_deriv ?_
    have hs : Real.sqrt (1 + (v / η) ^ 2) = Real.sqrt (η ^ 2 + v ^ 2) / η := by
      have h1 : (1 : ℝ) + (v / η) ^ 2 = (η ^ 2 + v ^ 2) / η ^ 2 := by
        field_simp
      rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hη.le]
    rw [hs]
    field_simp
  have hcont : Continuous fun v : ℝ ↦ 1 / Real.sqrt (η ^ 2 + v ^ 2) := by
    refine continuous_const.div (by fun_prop) fun v ↦ ?_
    have : (0:ℝ) < η ^ 2 + v ^ 2 := by positivity
    exact ne_of_gt (Real.sqrt_pos.mpr this)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ ↦ hderiv v)
    (hcont.intervalIntegrable _ _)]
  simp

/-- `∫₀^{1/2} (e^{Lv} - 1)/v dv = EiAux(L/2)`, by `w = Lv`. -/
theorem integral_eiAux_scaled {L : ℝ} (hL : 0 < L) :
    (∫ v in (0:ℝ)..(1/2 : ℝ), (Real.exp (L * v) - 1) / v) = EiAux (L / 2) := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (1/2 : ℝ))
    (fun w : ℝ ↦ (Real.exp w - 1) / w) (ne_of_gt hL)
  have heq : ∀ v : ℝ, (Real.exp (L * v) - 1) / v = L * ((Real.exp (L * v) - 1) / (L * v)) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · field_simp
  rw [intervalIntegral.integral_congr
      (g := fun v : ℝ ↦ L * ((Real.exp (L * v) - 1) / (L * v))) (fun v _ ↦ heq v),
    intervalIntegral.integral_const_mul, h]
  rw [EiAux, smul_eq_mul, mul_zero, show L * (1/2 : ℝ) = L / 2 by ring]
  field_simp

/-- `∫₀^{1/2} e^{Lv} dv = (e^{L/2} - 1)/L`. -/
theorem integral_exp_mul {L : ℝ} (hL : 0 < L) :
    (∫ v in (0:ℝ)..(1/2 : ℝ), Real.exp (L * v)) = (Real.exp (L / 2) - 1) / L := by
  have hderiv : ∀ v : ℝ, HasDerivAt (fun w : ℝ ↦ Real.exp (L * w) / L) (Real.exp (L * v)) v := by
    intro v
    have hinner : HasDerivAt (fun w : ℝ ↦ L * w) L v := by
      simpa using (hasDerivAt_id v).const_mul L
    have h := ((Real.hasDerivAt_exp (L * v)).comp v hinner).div_const L
    rw [Function.comp_def] at h
    refine h.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ ↦ hderiv v)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp
  field_simp

/-- `∫_{1/2}^∞ u e^{-Lu} du = e^{-L/2}(1/(2L) + 1/L²)`. -/
theorem integrableOn_id_mul_exp_neg {L : ℝ} (hL : 0 < L) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u * Real.exp (-(L * u))) (Set.Ioi (1/2 : ℝ)) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ 2 / L * Real.exp (-(L / 2) * u)) (Set.Ioi (1/2 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(L / 2) < 0) _).const_mul _
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg)).aestronglyMeasurable.restrict
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) < u := lt_trans (by norm_num) hu
    have hkey : u * Real.exp (-(L / 2) * u) ≤ 2 / L := by
      have h1 : (L / 2) * u + 1 ≤ Real.exp ((L / 2) * u) := by
        have := Real.add_one_le_exp ((L / 2) * u)
        linarith
      have h2 : (0:ℝ) < Real.exp ((L / 2) * u) := Real.exp_pos _
      have h3 : Real.exp (-(L / 2) * u) = 1 / Real.exp ((L / 2) * u) := by
        rw [show -(L / 2) * u = -((L / 2) * u) by ring, Real.exp_neg, one_div]
      rw [h3, mul_one_div, div_le_div_iff₀ h2 (by linarith)]
      nlinarith [h1, hu0.le]
    have hexp : Real.exp (-(L * u)) = Real.exp (-(L / 2) * u) * Real.exp (-(L / 2) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hnn : (0:ℝ) ≤ u * Real.exp (-(L * u)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hexp]
    have hE : (0:ℝ) < Real.exp (-(L / 2) * u) := Real.exp_pos _
    calc u * (Real.exp (-(L / 2) * u) * Real.exp (-(L / 2) * u))
        = (u * Real.exp (-(L / 2) * u)) * Real.exp (-(L / 2) * u) := by ring
      _ ≤ (2 / L) * Real.exp (-(L / 2) * u) := by
          exact mul_le_mul_of_nonneg_right hkey hE.le

/-- `∫_{1/2}^∞ u e^{-Lu} du = e^{-L/2}(1/(2L) + 1/L²)`. -/
theorem integral_id_mul_exp_neg_Ioi {L : ℝ} (hL : 0 < L) :
    (∫ u in Set.Ioi (1/2 : ℝ), u * Real.exp (-(L * u)))
      = Real.exp (-(L / 2)) * (1 / (2 * L) + 1 / L ^ 2) := by
  have hderiv : ∀ u ∈ Set.Ici (1/2 : ℝ),
      HasDerivAt (fun w : ℝ ↦ -(Real.exp (-(L * w)) * (w / L + 1 / L ^ 2)))
        (u * Real.exp (-(L * u))) u := by
    intro u _
    have hid : HasDerivAt (fun w : ℝ ↦ L * w) L u := by
      simpa using (hasDerivAt_id u).const_mul L
    have hinner : HasDerivAt (fun w : ℝ ↦ -(L * w)) (-L) u := hid.neg
    have he : HasDerivAt (fun w : ℝ ↦ Real.exp (-(L * w))) (Real.exp (-(L * u)) * -L) u := by
      have h := (Real.hasDerivAt_exp (-(L * u))).comp u hinner
      rw [Function.comp_def] at h
      exact h.congr_deriv (by ring)
    have hp : HasDerivAt (fun w : ℝ ↦ w / L + 1 / L ^ 2) (1 / L) u := by
      simpa using ((hasDerivAt_id u).div_const L).add_const (1 / L ^ 2)
    have hm := (he.mul hp).neg
    refine hm.congr_deriv ?_
    field_simp
    ring
  have ht : Filter.Tendsto (fun w : ℝ ↦ -(Real.exp (-(L * w)) * (w / L + 1 / L ^ 2)))
      Filter.atTop (nhds 0) := by
    have hcomp : Filter.Tendsto (fun w : ℝ ↦ L * w) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hL Filter.tendsto_id
    have h1 : Filter.Tendsto (fun y : ℝ ↦ y * Real.exp (-y)) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h0 : Filter.Tendsto (fun y : ℝ ↦ Real.exp (-y)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have hsum : Filter.Tendsto
        (fun y : ℝ ↦ -(1 / L ^ 2 * (y * Real.exp (-y))) + -(1 / L ^ 2 * Real.exp (-y)))
        Filter.atTop (nhds 0) := by
      have ha := (h1.const_mul (1 / L ^ 2)).neg
      have hb := (h0.const_mul (1 / L ^ 2)).neg
      simpa using ha.add hb
    have hcc := hsum.comp hcomp
    refine hcc.congr fun w ↦ ?_
    simp only [Function.comp_apply]
    field_simp
    ring
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_id_mul_exp_neg hL) ht]
  have : L * (1/2 : ℝ) = L / 2 := by ring
  rw [this]
  field_simp
  ring

/-! ### `lem:rameau`

`∫₀^∞ u x^{-u}/√(η² + (½-u)²) du`, in the `L = log x` parametrisation. The `(0,½)` half becomes,
under `v = ½ - u`, `e^{-L/2} ∫₀^{1/2} (½ + g(v))/√(η²+v²) dv` with `g(v) = (½-v)e^{Lv} - ½`, and the
constant `½` gives the `arsinh`. What is left of `g` is bounded by `g(v)/v`, whose integral is
`½ EiAux(L/2) - (e^{L/2}-1)/L` — except near `v = ½`, where `g` may turn negative and one drops the
`-½` first, at the cost of `-½ log(1-2/L)`.

The cut is at `v = ½ - 1/L`, and `g ≥ 0` to its left because `e^{Lv}(1-2v) ≥ (1+Lv)(1-2v) ≥ 1`
exactly when `v ≤ ½ - 1/L`. -/

/-- Measurable and bounded on `Ioc a b` is enough. Used where the integrand has a removable
singularity and `ContinuousOn` is unavailable. -/
theorem intervalIntegrable_of_bound {f : ℝ → ℝ} {a b C : ℝ} (hle : a ≤ b)
    (hm : Measurable f) (hb : ∀ v ∈ Set.Ioc a b, |f v| ≤ C) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ ↦ C)
    (MeasureTheory.integrableOn_const (by simp) (by simp)) hm.aestronglyMeasurable.restrict ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv
  rw [Real.norm_eq_abs]
  exact hb v hv

/-- The `lem:rameau` integrand, with `x^{-u}` written as `e^{-Lu}`. -/
noncomputable def rameauF (L η u : ℝ) : ℝ :=
  u * Real.exp (-(L * u)) / Real.sqrt (η ^ 2 + (1 / 2 - u) ^ 2)

/-- `g(v) = (½ - v) e^{Lv} - ½`, what is left of the `(0,½)` integrand after the `arsinh`. -/
noncomputable def rameauG (L v : ℝ) : ℝ := (1 / 2 - v) * Real.exp (L * v) - 1 / 2

/-- **`g ≥ 0` up to the cut**, because `(1 + Lv)(1 - 2v) ≥ 1` exactly for `v ≤ ½ - 1/L`. -/
theorem rameauG_nonneg {L v : ℝ} (hL : 0 < L) (hv0 : 0 ≤ v) (hv : v ≤ 1 / 2 - 1 / L) :
    0 ≤ rameauG L v := by
  have h1 : 1 + L * v ≤ Real.exp (L * v) := by
    have := Real.add_one_le_exp (L * v)
    linarith
  have hv2 : (0:ℝ) ≤ 1 / 2 - v := by
    have : (0:ℝ) < 1 / L := by positivity
    linarith
  have hkey : (1 + L * v) * (1 / 2 - v) ≥ 1 / 2 := by
    have hLv : L * v ≤ L * (1 / 2 - 1 / L) := by nlinarith
    have hLv' : L * (1 / 2 - 1 / L) = L / 2 - 1 := by field_simp
    nlinarith [hv0, hv2, mul_nonneg hv0 (sub_nonneg.mpr hv)]
  have hmul : (1 + L * v) * (1 / 2 - v) ≤ Real.exp (L * v) * (1 / 2 - v) :=
    mul_le_mul_of_nonneg_right h1 hv2
  rw [rameauG]
  nlinarith [hkey, hmul]

/-- `g(v)/v = ½(e^{Lv} - 1)/v - e^{Lv}` away from `0`. -/
theorem rameauG_div {L v : ℝ} (hv : v ≠ 0) :
    rameauG L v / v = (Real.exp (L * v) - 1) / v / 2 - Real.exp (L * v) := by
  rw [rameauG]
  field_simp
  ring

/-- `0 ≤ (e^{Lv} - 1)/v ≤ L e^{Lv}` for `v > 0`, which bounds `g(v)/v`. -/
theorem exp_sub_one_div_bounds {L v : ℝ} (hL : 0 < L) (hv : 0 < v) :
    0 ≤ (Real.exp (L * v) - 1) / v ∧ (Real.exp (L * v) - 1) / v ≤ L * Real.exp (L * v) := by
  constructor
  · have h1 : (1:ℝ) ≤ Real.exp (L * v) := Real.one_le_exp (by positivity)
    positivity
  · have h := sub_one_div_le_exp (le_of_lt (by positivity : (0:ℝ) < L * v))
    rw [div_le_iff₀ (by positivity : (0:ℝ) < L * v)] at h
    rw [div_le_iff₀ hv]
    nlinarith [h]

theorem intervalIntegrable_rameauG_div {L : ℝ} (hL : 0 < L) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    IntervalIntegrable (fun v : ℝ ↦ rameauG L v / v) MeasureTheory.volume a b := by
  refine intervalIntegrable_of_bound hab (by unfold rameauG; fun_prop)
    (C := (L / 2 + 1) * Real.exp (L / 2)) ?_
  intro v hv
  have hv0 : (0:ℝ) < v := lt_of_le_of_lt ha hv.1
  have hv2 : v ≤ 1 / 2 := le_trans hv.2 hb
  obtain ⟨hnn, hup⟩ := exp_sub_one_div_bounds hL hv0
  have hexp : Real.exp (L * v) ≤ Real.exp (L / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hE : (0:ℝ) < Real.exp (L * v) := Real.exp_pos _
  rw [rameauG_div (ne_of_gt hv0), abs_le]
  constructor <;> nlinarith [hnn, hup, hexp, hE, Real.exp_pos (L / 2)]

/-- `∫₀^{1/2} g(v)/v dv = ½ EiAux(L/2) - (e^{L/2} - 1)/L`. -/
theorem integral_rameauG_div {L : ℝ} (hL : 0 < L) :
    (∫ v in (0:ℝ)..(1/2 : ℝ), rameauG L v / v)
      = EiAux (L / 2) / 2 - (Real.exp (L / 2) - 1) / L := by
  have hi1 : IntervalIntegrable (fun v : ℝ ↦ (Real.exp (L * v) - 1) / v / 2)
      MeasureTheory.volume 0 (1/2 : ℝ) := by
    refine intervalIntegrable_of_bound (by norm_num) (by fun_prop)
      (C := L * Real.exp (L / 2) / 2) ?_
    intro v hv
    have hv0 : (0:ℝ) < v := hv.1
    obtain ⟨hnn, hup⟩ := exp_sub_one_div_bounds hL hv0
    have hexp : Real.exp (L * v) ≤ Real.exp (L / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hv.2]
    rw [abs_le]
    constructor <;> nlinarith [Real.exp_pos (L * v)]
  have hi2 : IntervalIntegrable (fun v : ℝ ↦ Real.exp (L * v)) MeasureTheory.volume 0 (1/2 : ℝ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hcongr : (∫ v in (0:ℝ)..(1/2 : ℝ), rameauG L v / v)
      = ∫ v in (0:ℝ)..(1/2 : ℝ), ((Real.exp (L * v) - 1) / v / 2 - Real.exp (L * v)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun v hv ↦ ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hv
    exact rameauG_div (ne_of_gt hv.1)
  rw [hcongr, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_div,
    integral_eiAux_scaled hL, integral_exp_mul hL]

/-- `v ≤ √(η² + v²)`. -/
theorem le_sqrt_sq_add_sq {η v : ℝ} (hv : 0 ≤ v) : v ≤ Real.sqrt (η ^ 2 + v ^ 2) := by
  rw [show v = Real.sqrt (v ^ 2) from (Real.sqrt_sq hv).symm]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [sq_nonneg η, Real.sq_sqrt (sq_nonneg v)]

/-- **The `g`-part of the `(0,½)` half.** -/
theorem rameauK_le {L η : ℝ} (hL : 7 ≤ L) (hη0 : 0 < η) :
    (∫ v in (0:ℝ)..(1/2 : ℝ), rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))
      ≤ EiAux (L / 2) / 2 - (Real.exp (L / 2) - 1) / L - Real.log (1 - 2 / L) / 2 := by
  have hL0 : (0:ℝ) < L := by linarith
  have hinvL : 1 / L ≤ 1 / 7 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  have hinvL0 : (0:ℝ) < 1 / L := by positivity
  set c : ℝ := 1 / 2 - 1 / L with hcdef
  have hc0 : (0:ℝ) < c := by rw [hcdef]; linarith
  have hc2 : c ≤ 1 / 2 := by rw [hcdef]; linarith
  have hsq : ∀ v : ℝ, (0:ℝ) < Real.sqrt (η ^ 2 + v ^ 2) := by
    intro v
    exact Real.sqrt_pos.mpr (by positivity)
  have hcontK : Continuous fun v : ℝ ↦ rameauG L v / Real.sqrt (η ^ 2 + v ^ 2) := by
    refine Continuous.div (by unfold rameauG; fun_prop) (by fun_prop) fun v ↦ ne_of_gt (hsq v)
  have hK1 : IntervalIntegrable (fun v : ℝ ↦ rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))
      MeasureTheory.volume 0 c := hcontK.intervalIntegrable 0 c
  have hK2 : IntervalIntegrable (fun v : ℝ ↦ rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))
      MeasureTheory.volume c (1/2 : ℝ) := hcontK.intervalIntegrable c (1/2 : ℝ)
  have hsplitK : (∫ v in (0:ℝ)..(1/2 : ℝ), rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))
      = (∫ v in (0:ℝ)..c, rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))
        + ∫ v in c..(1/2 : ℝ), rameauG L v / Real.sqrt (η ^ 2 + v ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals hK1 hK2).symm
  -- the two `g/v` integrals
  have hG1 := intervalIntegrable_rameauG_div hL0 (le_refl (0:ℝ)) hc0.le hc2
  have hG2 := intervalIntegrable_rameauG_div hL0 hc0.le hc2 (le_refl (1/2 : ℝ))
  have hGsum : (∫ v in (0:ℝ)..c, rameauG L v / v) + (∫ v in c..(1/2 : ℝ), rameauG L v / v)
      = EiAux (L / 2) / 2 - (Real.exp (L / 2) - 1) / L := by
    rw [intervalIntegral.integral_add_adjacent_intervals hG1 hG2, integral_rameauG_div hL0]
  -- left of the cut
  have hleft : (∫ v in (0:ℝ)..c, rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))
      ≤ ∫ v in (0:ℝ)..c, rameauG L v / v := by
    refine intervalIntegral.integral_mono_on hc0.le hK1 hG1 fun v hv ↦ ?_
    have hv0 : (0:ℝ) ≤ v := hv.1
    rcases eq_or_lt_of_le hv0 with h | h
    · rw [← h]
      simp [rameauG]
    · have hvc : v ≤ 1 / 2 - 1 / L := by
        have h2 : v ≤ c := hv.2
        linarith
      have hg : 0 ≤ rameauG L v := rameauG_nonneg hL0 hv0 hvc
      have hle : v ≤ Real.sqrt (η ^ 2 + v ^ 2) := le_sqrt_sq_add_sq hv0
      exact div_le_div_of_nonneg_left hg h hle
  -- right of the cut
  have hne : ∀ v ∈ Set.uIcc c (1/2 : ℝ), v ≠ 0 := by
    intro v hv
    rw [Set.uIcc_of_le hc2] at hv
    have h1 : c ≤ v := hv.1
    exact ne_of_gt (by linarith)
  have hcontR : ContinuousOn (fun v : ℝ ↦ rameauG L v / v + 1 / 2 / v) (Set.uIcc c (1/2 : ℝ)) :=
    ContinuousOn.add (ContinuousOn.div (by unfold rameauG; fun_prop) (by fun_prop) hne)
      (ContinuousOn.div continuousOn_const (by fun_prop) hne)
  have hR : IntervalIntegrable (fun v : ℝ ↦ rameauG L v / v + 1 / 2 / v)
      MeasureTheory.volume c (1/2 : ℝ) := hcontR.intervalIntegrable
  have hright : (∫ v in c..(1/2 : ℝ), rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))
      ≤ ∫ v in c..(1/2 : ℝ), (rameauG L v / v + 1 / 2 / v) := by
    refine intervalIntegral.integral_mono_on hc2 hK2 hR fun v hv ↦ ?_
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hc0 hv.1
    have hle : v ≤ Real.sqrt (η ^ 2 + v ^ 2) := le_sqrt_sq_add_sq hv0.le
    rcases le_or_gt 0 (rameauG L v) with hg | hg
    · have h1 : rameauG L v / Real.sqrt (η ^ 2 + v ^ 2) ≤ rameauG L v / v :=
        div_le_div_of_nonneg_left hg hv0 hle
      have h2 : (0:ℝ) ≤ 1 / 2 / v := by positivity
      linarith
    · have h1 : rameauG L v / Real.sqrt (η ^ 2 + v ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hg.le (hsq v).le
      have h2 : (0:ℝ) ≤ rameauG L v / v + 1 / 2 / v := by
        have heq : rameauG L v / v + 1 / 2 / v = (1 / 2 - v) * Real.exp (L * v) / v := by
          rw [rameauG]
          field_simp
          ring
        rw [heq]
        have : (0:ℝ) ≤ 1 / 2 - v := by linarith [hv.2]
        positivity
      linarith
  have hRsplit : (∫ v in c..(1/2 : ℝ), (rameauG L v / v + 1 / 2 / v))
      = (∫ v in c..(1/2 : ℝ), rameauG L v / v) + ∫ v in c..(1/2 : ℝ), 1 / 2 / v := by
    exact intervalIntegral.integral_add hG2
      (ContinuousOn.intervalIntegrable
        (ContinuousOn.div continuousOn_const (by fun_prop) hne))
  have hlog : (∫ v in c..(1/2 : ℝ), 1 / 2 / v) = -(Real.log (1 - 2 / L)) / 2 := by
    have hdiv : ∀ v : ℝ, (1:ℝ) / 2 / v = (1 / 2) * (1 / v) := by intro v; ring
    rw [intervalIntegral.integral_congr (g := fun v : ℝ ↦ (1/2 : ℝ) * (1 / v))
        (fun v _ ↦ hdiv v), intervalIntegral.integral_const_mul]
    have hnot : (0:ℝ) ∉ Set.uIcc c (1/2 : ℝ) := by
      rw [Set.uIcc_of_le hc2]
      intro hmem
      exact absurd hmem.1 (by linarith)
    rw [integral_one_div hnot]
    have harg : (1/2 : ℝ) / c = (1 - 2 / L)⁻¹ := by
      rw [hcdef]
      field_simp
    rw [harg, Real.log_inv]
    ring
  rw [hRsplit, hlog] at hright
  rw [hsplitK]
  linarith [hleft, hright, hGsum]

theorem le_sqrt_sq_add_sq_left {a b : ℝ} (ha : 0 ≤ a) : a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [show a = Real.sqrt (a ^ 2) from (Real.sqrt_sq ha).symm]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [sq_nonneg b, Real.sq_sqrt (sq_nonneg a)]

theorem continuous_rameauF {L η : ℝ} (hη0 : 0 < η) : Continuous (rameauF L η) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun u ↦ ?_
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

/-- **The `(0,½)` half of `lem:rameau`.** -/
theorem rameau_head {L η : ℝ} (hL : 7 ≤ L) (hη0 : 0 < η) :
    (∫ u in (0:ℝ)..(1/2 : ℝ), rameauF L η u)
      ≤ Real.exp (-(L / 2)) * (Real.arsinh (1 / 2 / η) / 2
          + (EiAux (L / 2) / 2 - (Real.exp (L / 2) - 1) / L - Real.log (1 - 2 / L) / 2)) := by
  have hsq : ∀ v : ℝ, (0:ℝ) < Real.sqrt (η ^ 2 + v ^ 2) := fun v ↦
    Real.sqrt_pos.mpr (by positivity)
  have hcv : (∫ u in (0:ℝ)..(1/2 : ℝ), rameauF L η u)
      = ∫ v in (0:ℝ)..(1/2 : ℝ), rameauF L η (1/2 - v) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := (1/2 : ℝ))
      (fun u : ℝ ↦ rameauF L η u) (1/2 : ℝ)
    simpa using h.symm
  have hval : ∀ v : ℝ, rameauF L η (1/2 - v)
      = Real.exp (-(L / 2)) * (1 / Real.sqrt (η ^ 2 + v ^ 2) / 2)
        + Real.exp (-(L / 2)) * (rameauG L v / Real.sqrt (η ^ 2 + v ^ 2)) := by
    intro v
    have h1 : (1:ℝ) / 2 - (1 / 2 - v) = v := by ring
    have h2 : Real.exp (-(L * (1 / 2 - v))) = Real.exp (-(L / 2)) * Real.exp (L * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [rameauF, rameauG, h1, h2]
    ring
  have hIa : IntervalIntegrable
      (fun v : ℝ ↦ Real.exp (-(L / 2)) * (1 / Real.sqrt (η ^ 2 + v ^ 2) / 2))
      MeasureTheory.volume 0 (1/2 : ℝ) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul
      ((Continuous.div continuous_const (by fun_prop) fun v ↦ ne_of_gt (hsq v)).div_const 2)
  have hIb : IntervalIntegrable
      (fun v : ℝ ↦ Real.exp (-(L / 2)) * (rameauG L v / Real.sqrt (η ^ 2 + v ^ 2)))
      MeasureTheory.volume 0 (1/2 : ℝ) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul
      (Continuous.div (by unfold rameauG; fun_prop) (by fun_prop) fun v ↦ ne_of_gt (hsq v))
  rw [hcv, intervalIntegral.integral_congr (g := fun v : ℝ ↦
      Real.exp (-(L / 2)) * (1 / Real.sqrt (η ^ 2 + v ^ 2) / 2)
        + Real.exp (-(L / 2)) * (rameauG L v / Real.sqrt (η ^ 2 + v ^ 2))) (fun v _ ↦ hval v),
    intervalIntegral.integral_add hIa hIb, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    integral_one_div_sqrt_sq_add_sq hη0]
  have hK := rameauK_le hL hη0
  have hE : (0:ℝ) < Real.exp (-(L / 2)) := Real.exp_pos _
  nlinarith [hK, hE]

/-- The `1/√x` bookkeeping: `½ arsinh(1/2η) + 1/L - ½log(1-2/L) ≤ 1 + ½log(1/η)`.

This is where the paper's `γ/2 + ½ log(L/2)` goes. The `arsinh` exceeds `log(1/η)` by
`log((1+√(4η²+1))/2) ≤ log 3.27 ≤ 3.27/e`, and `1/L + ½|log(1-2/L)| ≤ 1/7 + 1/5` at `L ≥ 7`. -/
theorem rameau_const {L η : ℝ} (hL : 7 ≤ L) (hη0 : 0 < η) (hη : η ≤ Real.exp 1) :
    Real.arsinh (1 / 2 / η) / 2 + 1 / L - Real.log (1 - 2 / L) / 2
      ≤ 1 + Real.log (1 / η) / 2 := by
  have hL0 : (0:ℝ) < L := by linarith
  have he2 : η ^ 2 ≤ 7.39 := by
    have h := Real.exp_one_lt_d9
    nlinarith [hη0, hη]
  have hsq : Real.sqrt (1 + (1 / 2 / η) ^ 2) ≤ 2.77 / η := by
    have hb : (1:ℝ) + (1 / 2 / η) ^ 2 ≤ (2.77 / η) ^ 2 := by
      have hη2 : (0:ℝ) < η ^ 2 := by positivity
      rw [← sub_nonneg]
      have heq : (2.77 / η) ^ 2 - (1 + (1 / 2 / η) ^ 2)
          = (2.77 ^ 2 - 1 / 4 - η ^ 2) / η ^ 2 := by
        field_simp
        ring
      rw [heq]
      refine div_nonneg ?_ hη2.le
      nlinarith [he2]
    calc Real.sqrt (1 + (1 / 2 / η) ^ 2) ≤ Real.sqrt ((2.77 / η) ^ 2) := Real.sqrt_le_sqrt hb
      _ = 2.77 / η := Real.sqrt_sq (by positivity)
  have harsinh : Real.arsinh (1 / 2 / η) ≤ Real.log (3.27 / η) := by
    rw [Real.arsinh]
    refine Real.log_le_log (by positivity) ?_
    have hsum : (1:ℝ) / 2 / η + 2.77 / η = 3.27 / η := by
      field_simp
      ring
    linarith [hsq, hsum.le, hsum.ge]
  have hlogdiv : Real.log (3.27 / η) = Real.log 3.27 + Real.log (1 / η) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hη0), one_div, Real.log_inv]
    ring
  have hlog327 : Real.log 3.27 ≤ 1.203 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3.27 / Real.exp 1 by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_ne_zero 1), Real.log_exp] at h
    have he := Real.exp_one_gt_d9
    have hdiv : (3.27:ℝ) / Real.exp 1 ≤ 3.27 / 2.7182818283 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have hnum : (3.27:ℝ) / 2.7182818283 ≤ 2.203 := by norm_num
    linarith
  have hLm : (5:ℝ) ≤ L - 2 := by linarith
  have h2L : (0:ℝ) < 1 - 2 / L := by
    rw [sub_pos, div_lt_one hL0]
    linarith
  have hloglow : -(2 / (L - 2)) ≤ Real.log (1 - 2 / L) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - 2 / L)⁻¹ by positivity)
    rw [Real.log_inv] at h
    have heq : (1 - 2 / L)⁻¹ - 1 = 2 / (L - 2) := by
      field_simp
      ring
    rw [heq] at h
    linarith
  have hinv1 : 1 / L ≤ 1 / 7 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  have hinv2 : 2 / (L - 2) ≤ 2 / 5 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith [harsinh, hlogdiv.le, hlogdiv.ge, hlog327, hloglow, hinv1, hinv2]

/-- **`lem:rameau`**, `eq:arguc2`: the integral for `0 < η ≤ e` and `L = log x ≥ 7`.

The paper's `1/√x` coefficient is `½log(1/η) + (1+2/L)/(2ηL)`; this one carries an extra `1`, which
absorbs the `γ/2 + ½ log(L/2)` the paper keeps. The `√x` terms have room to spare downstream — in
`prop:sagaro` they end up below `10⁻⁴/(6π) · log(T/2π)` — so it costs nothing. -/
theorem rameau {L η : ℝ} (hL : 7 ≤ L) (hη0 : 0 < η) (hη : η ≤ Real.exp 1) :
    (∫ u in Set.Ioi (0:ℝ), rameauF L η u)
      ≤ 2 / L ^ 2 + 8 / L ^ 3 + 336 / L ^ 4
        + Real.exp (-(L / 2)) * (1 + Real.log (1 / η) / 2 + (1 + 2 / L) / (2 * η * L)) := by
  have hL0 : (0:ℝ) < L := by linarith
  have hcont := continuous_rameauF (L := L) (η := η) hη0
  have hbound : ∀ u ∈ Set.Ioi (1/2 : ℝ), ‖rameauF L η u‖ ≤ 1 / η * (u * Real.exp (-(L * u))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := lt_trans (by norm_num) hu
    have hden : η ≤ Real.sqrt (η ^ 2 + (1 / 2 - u) ^ 2) := le_sqrt_sq_add_sq_left hη0.le
    have hnum : (0:ℝ) ≤ u * Real.exp (-(L * u)) := by positivity
    have hnn : (0:ℝ) ≤ rameauF L η u := by
      rw [rameauF]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, rameauF, div_le_iff₀ (by positivity)]
    have hcancel : 1 / η * (u * Real.exp (-(L * u))) * η = u * Real.exp (-(L * u)) := by
      field_simp
    nlinarith [hnum, hden, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 1 / η) hnum)
      (sub_nonneg.mpr hden)]
  have hFint : MeasureTheory.IntegrableOn (rameauF L η) (Set.Ioi (1/2 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' ((integrableOn_id_mul_exp_neg hL0).const_mul (1 / η))
      hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact hbound u hu
  have htail : (∫ u in Set.Ioi (1/2 : ℝ), rameauF L η u)
      ≤ 1 / η * (Real.exp (-(L / 2)) * (1 / (2 * L) + 1 / L ^ 2)) := by
    have hmono : (∫ u in Set.Ioi (1/2 : ℝ), rameauF L η u)
        ≤ ∫ u in Set.Ioi (1/2 : ℝ), 1 / η * (u * Real.exp (-(L * u))) := by
      refine MeasureTheory.setIntegral_mono_on hFint
        ((integrableOn_id_mul_exp_neg hL0).const_mul (1 / η)) measurableSet_Ioi fun u hu ↦ ?_
      have h := hbound u hu
      rw [Real.norm_eq_abs] at h
      exact le_trans (le_abs_self _) h
    rw [MeasureTheory.integral_const_mul, integral_id_mul_exp_neg_Ioi hL0] at hmono
    exact hmono
  have hIoc : MeasureTheory.IntegrableOn (rameauF L η) (Set.Ioc (0:ℝ) (1/2)) := by
    have h : IntervalIntegrable (rameauF L η) MeasureTheory.volume (0:ℝ) (1/2 : ℝ) :=
      hcont.intervalIntegrable _ _
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  have hsplit : (∫ u in Set.Ioi (0:ℝ), rameauF L η u)
      = (∫ u in (0:ℝ)..(1/2 : ℝ), rameauF L η u) + ∫ u in Set.Ioi (1/2 : ℝ), rameauF L η u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
      ← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hFint,
      Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1/2)]
  have hhead := rameau_head hL hη0
  have hX : (1:ℝ) ≤ L / 2 := by linarith
  have hei := eiAux_le hX
  have hEE : Real.exp (-(L / 2)) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hE : (0:ℝ) < Real.exp (-(L / 2)) := Real.exp_pos _
  have heiE : Real.exp (-(L / 2)) * (EiAux (L / 2) / 2)
      ≤ 1 / L + 2 / L ^ 2 + 8 / L ^ 3 + 336 / L ^ 4 := by
    have h1 : Real.exp (-(L / 2)) * (EiAux (L / 2) / 2)
        ≤ Real.exp (-(L / 2)) * (Real.exp (L / 2)
          * (1 / (L / 2) + 1 / (L / 2) ^ 2 + 2 / (L / 2) ^ 3 + 42 / (L / 2) ^ 4) / 2) := by
      have h := mul_le_mul_of_nonneg_left hei hE.le
      linarith [h]
    have h2 : Real.exp (-(L / 2)) * (Real.exp (L / 2)
        * (1 / (L / 2) + 1 / (L / 2) ^ 2 + 2 / (L / 2) ^ 3 + 42 / (L / 2) ^ 4) / 2)
        = 1 / L + 2 / L ^ 2 + 8 / L ^ 3 + 336 / L ^ 4 := by
      rw [show Real.exp (-(L / 2)) * (Real.exp (L / 2)
          * (1 / (L / 2) + 1 / (L / 2) ^ 2 + 2 / (L / 2) ^ 3 + 42 / (L / 2) ^ 4) / 2)
          = (Real.exp (-(L / 2)) * Real.exp (L / 2))
            * ((1 / (L / 2) + 1 / (L / 2) ^ 2 + 2 / (L / 2) ^ 3 + 42 / (L / 2) ^ 4) / 2) by ring,
        hEE]
      field_simp
      ring
    linarith [h1, h2.le, h2.ge]
  have hsub : Real.exp (-(L / 2)) * (-((Real.exp (L / 2) - 1) / L))
      = -(1 / L) + Real.exp (-(L / 2)) * (1 / L) := by
    rw [show Real.exp (-(L / 2)) * (-((Real.exp (L / 2) - 1) / L))
        = -((Real.exp (-(L / 2)) * Real.exp (L / 2)) / L) + Real.exp (-(L / 2)) * (1 / L) by ring,
      hEE]
  have hconst := mul_le_mul_of_nonneg_left (rameau_const hL hη0 hη) hE.le
  have hetaform : 1 / η * (Real.exp (-(L / 2)) * (1 / (2 * L) + 1 / L ^ 2))
      = Real.exp (-(L / 2)) * ((1 + 2 / L) / (2 * η * L)) := by
    field_simp
  have hexpand : Real.exp (-(L / 2)) * (Real.arsinh (1 / 2 / η) / 2
        + (EiAux (L / 2) / 2 - (Real.exp (L / 2) - 1) / L - Real.log (1 - 2 / L) / 2))
      = Real.exp (-(L / 2)) * (EiAux (L / 2) / 2)
        + Real.exp (-(L / 2)) * (-((Real.exp (L / 2) - 1) / L))
        + Real.exp (-(L / 2)) * (Real.arsinh (1 / 2 / η) / 2 + 1 / L
            - Real.log (1 - 2 / L) / 2)
        - Real.exp (-(L / 2)) * (1 / L) := by ring
  have hlast : Real.exp (-(L / 2)) * (1 + Real.log (1 / η) / 2)
      + Real.exp (-(L / 2)) * ((1 + 2 / L) / (2 * η * L))
      = Real.exp (-(L / 2)) * (1 + Real.log (1 / η) / 2 + (1 + 2 / L) / (2 * η * L)) := by ring
  rw [hexpand] at hhead
  rw [hetaform] at htail
  rw [hsplit]
  linarith [hhead, htail, heiE, hsub.le, hsub.ge, hconst, hlast.le, hlast.ge]

end CH2Section81
