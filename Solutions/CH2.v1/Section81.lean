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

end CH2Section81
