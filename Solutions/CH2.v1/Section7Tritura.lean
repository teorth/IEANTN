/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section7Weights

/-!
# Section 7: `prop:tritura`

With `F(u) = 1/π + (1-u) cot πu`, `f(u) = 1/(πu) - cot πu` and `w(u) = y + log u`,

`2π ∫_ε^b √(F(u)² + (1-u)²) w(u) du ≤ y² - w(ε)² - 2C₁(y+1) + 2C₂ + E(ε, b, y)`

for `0 < ε ≤ 1/2`, `ε ≤ b < 1`, `w(ε) ≥ 0`, with `C₁ = 0.1672 ≤ C₁^{true} = 0.16894…`,
`C₂ = 0.1729 ≥ C₂^{true} = 0.16418…`, and an explicit error `E` that vanishes as `ε → 0`, `b → 1`.

## How this differs from the paper

The paper integrates over `[ε, 1]` and evaluates `C₁`, `C₂` to six digits with Arb, then shows the
`[0, ε]` pieces have a sign by `lem:tremic`. Here the upper endpoint is `b < 1`, which keeps away from
the junk value of `F` at `1`; the consumer (`lem:adar`) sums over zeros below a height `t₁ < T` it may
take as close to `T` as it likes. The constants are one-sided and crude — a dozen terms of the
cotangent series for `C₁`, two for `C₂` — and the `[0, ε]` and `[b, 1]` pieces are bounded outright.
Section 9's budget has room for all of it: the `log(T/2π)` coefficient it needs is `2C₁ ≥ 1.001/3`.
-/

open Real MeasureTheory Set

namespace CH2Section7T

open CH2Section7

/-- `g(u) = (1-u)² f(u)/π`, the antiderivative of `F² + (1-u)² - 1/(πu)²`. -/
noncomputable def gT (u : ℝ) : ℝ := (1 - u) ^ 2 * freal u / Real.pi

theorem Fweight_eq_freal {u : ℝ} (hu : u ≠ 0) :
    Fweight u = 1 / (Real.pi * u) - (1 - u) * freal u := by
  rw [Fweight_eq, freal]
  field_simp
  ring

theorem sin_pi_ne_zero {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : Real.sin (Real.pi * u) ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'

theorem hasDerivAt_gT {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt gT (Fweight u ^ 2 + (1 - u) ^ 2 - 1 / (Real.pi * u) ^ 2) u := by
  have hπ := Real.pi_pos
  have hs := sin_pi_ne_zero h0 h1
  have hπu : HasDerivAt (fun v : ℝ ↦ Real.pi * v) Real.pi u := by
    simpa using (hasDerivAt_id u).const_mul Real.pi
  have hcot : HasDerivAt (fun v ↦ Real.cot (Real.pi * v))
      (-(1 / Real.sin (Real.pi * u) ^ 2) * Real.pi) u := (hasDerivAt_cot hs).comp u hπu
  have hinv : HasDerivAt (fun v : ℝ ↦ (Real.pi * v)⁻¹) (-(Real.pi) / (Real.pi * u) ^ 2) u :=
    hπu.inv (by positivity)
  have hf : HasDerivAt freal (-(Real.pi) / (Real.pi * u) ^ 2
      - -(1 / Real.sin (Real.pi * u) ^ 2) * Real.pi) u :=
    (hinv.sub hcot).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v ↦ by
      simp [freal, one_div])
  have hsq : HasDerivAt (fun v : ℝ ↦ (1 - v) ^ 2) (2 * (1 - u) * (-1)) u := by
    refine (((hasDerivAt_id u).const_sub 1).pow 2).congr_deriv ?_
    simp
  refine ((hsq.mul hf).div_const Real.pi).congr_deriv ?_
  -- the identity, with `1/sin² = 1 + cot²`
  have hcs : 1 / Real.sin (Real.pi * u) ^ 2 = 1 + Real.cot (Real.pi * u) ^ 2 := by
    rw [Real.cot_eq_cos_div_sin]
    have := Real.sin_sq_add_cos_sq (Real.pi * u)
    field_simp
    linarith
  rw [hcs, Fweight_eq, freal]
  field_simp
  ring

/-- `√X ≤ A + (X - A²)/(2A)` for `A > 0`, the concavity step `1_55pm`. -/
theorem sqrt_le_tangent {X A : ℝ} (hA : 0 < A) (hX : 0 ≤ X) : Real.sqrt X ≤ A + (X - A ^ 2) / (2 * A) := by
  have h : A + (X - A ^ 2) / (2 * A) = (X + A ^ 2) / (2 * A) := by field_simp; ring
  rw [h, le_div_iff₀ (by positivity)]
  have hs := Real.sq_sqrt hX
  nlinarith [sq_nonneg (Real.sqrt X - A), Real.sqrt_nonneg X]

/-! ### Bounds on `f` from the cotangent series -/

/-- The coefficients used for the lower bound: `ζ(2)`, `ζ(4)`, then `1`. -/
noncomputable def cLow (n : ℕ) : ℝ :=
  if n = 0 then Real.pi ^ 2 / 6 else if n = 1 then Real.pi ^ 4 / 90 else 1

theorem cLow_le_zeta (n : ℕ) : cLow n ≤ zetaReal (2 * (n : ℝ) + 2) := by
  unfold cLow
  split_ifs with h0 h1
  · subst h0; simp [← zetaReal_two_eq]
  · subst h1; norm_num [← zetaReal_four_eq]
  · exact one_le_zetaReal (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)

theorem cLow_nonneg (n : ℕ) : 0 ≤ cLow n := by
  unfold cLow; split_ifs <;> positivity

theorem freal_ge_partial (hcs : CotangentSeries.v1.cot_series_zeta_values) {u : ℝ} (h0 : 0 < u)
    (h1 : u < 1) (N : ℕ) :
    (2 / Real.pi) * ∑ n ∈ Finset.range N, cLow n * u ^ (2 * n + 1) ≤ freal u := by
  have H := hasSum_freal hcs h0 h1
  rw [Finset.mul_sum]
  calc ∑ n ∈ Finset.range N, 2 / Real.pi * (cLow n * u ^ (2 * n + 1))
      ≤ ∑ n ∈ Finset.range N, (2 / Real.pi) * zetaReal (2 * (n : ℝ) + 2) * u ^ (2 * n + 1) := by
        refine Finset.sum_le_sum fun n _ ↦ ?_
        rw [← mul_assoc]
        have := cLow_le_zeta n
        have : 0 ≤ u ^ (2 * n + 1) := by positivity
        have : 0 < 2 / Real.pi := by positivity
        gcongr
    _ ≤ freal u := sum_le_hasSum _ (fun n _ ↦ by
          have := zetaReal_pos (s := 2 * (n : ℝ) + 2) (by
            have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
          positivity) H

theorem freal_le (hcs : CotangentSeries.v1.cot_series_zeta_values) {u : ℝ} (h0 : 0 < u)
    (h1 : u < 1) :
    freal u ≤ (2 / Real.pi) * (Real.pi ^ 2 / 6 * u + Real.pi ^ 4 / 90 * (u ^ 3 / (1 - u ^ 2))) := by
  have H := hasSum_freal hcs h0 h1
  have hu2 : u ^ 2 < 1 := by nlinarith
  have hπ := Real.pi_pos
  have hgeo : HasSum (fun n : ℕ ↦ u * (u ^ 2) ^ n) (u / (1 - u ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hu2).mul_left u
    simpa [div_eq_mul_inv] using this
  have hsingle : HasSum (fun n : ℕ ↦ if n = 0 then (2 / Real.pi) * (zetaReal 2 - zetaReal 4) * u else 0)
      ((2 / Real.pi) * (zetaReal 2 - zetaReal 4) * u) := hasSum_ite_eq 0 _
  have hmaj := (hgeo.mul_left ((2 / Real.pi) * zetaReal 4)).add hsingle
  have hle := hasSum_le (fun n ↦ ?_) H hmaj
  · have hu1 : 1 - u ^ 2 ≠ 0 := by linarith
    have e : (2 / Real.pi) * zetaReal 4 * (u / (1 - u ^ 2)) + (2 / Real.pi) * (zetaReal 2 - zetaReal 4) * u
        = (2 / Real.pi) * (Real.pi ^ 2 / 6 * u + Real.pi ^ 4 / 90 * (u ^ 3 / (1 - u ^ 2))) := by
      rw [zetaReal_two_eq, zetaReal_four_eq]
      field_simp
      ring
    linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, mul_one, if_true, pow_one]
      ring_nf; rfl
    · rw [if_neg hn.ne', add_zero, ← pow_mul, ← pow_succ']
      have hz : zetaReal (2 * (n : ℝ) + 2) ≤ zetaReal 4 :=
        zetaReal_le (by norm_num) (by have : (1:ℝ) ≤ n := by exact_mod_cast hn
                                      linarith)
      have : 0 ≤ u ^ (2 * n + 1) := by positivity
      have h2 : 2 * n + 1 = 2 * n + 1 := rfl
      calc 2 / Real.pi * zetaReal (2 * (n : ℝ) + 2) * u ^ (2 * n + 1)
          ≤ 2 / Real.pi * zetaReal 4 * u ^ (2 * n + 1) := by gcongr

/-! ### Integral bounds on `[ε, b]` -/

theorem gT_nonneg (hcs : CotangentSeries.v1.cot_series_zeta_values) {u : ℝ} (h0 : 0 < u)
    (h1 : u < 1) : 0 ≤ gT u := by
  have := freal_pos hcs h0 h1
  unfold gT; positivity

theorem continuousOn_freal {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContinuousOn freal (Set.Icc a b) := by
  intro u hu
  have h0 : 0 < u := by linarith [hu.1]
  have h1 : u < 1 := by linarith [hu.2]
  refine ContinuousAt.continuousWithinAt ?_
  have hs := sin_pi_ne_zero h0 h1
  unfold freal
  have hc : ContinuousAt (fun v : ℝ ↦ Real.cot (Real.pi * v)) u := by
    simp only [Real.cot_eq_cos_div_sin]
    exact (by fun_prop : ContinuousAt (fun v : ℝ ↦ Real.cos (Real.pi * v)) u).div
      (by fun_prop) hs
  exact (continuousAt_const.div (by fun_prop) (by positivity)).sub hc

theorem continuousOn_gT {a b : ℝ} (ha : 0 < a) (hb : b < 1) : ContinuousOn gT (Set.Icc a b) := by
  unfold gT
  exact ((continuousOn_const.sub continuousOn_id).pow 2 |>.mul (continuousOn_freal ha hb)).div_const _

/-- `∫_0^1 (1-u)² u^{2n+1} = 1/(2n+2) - 2/(2n+3) + 1/(2n+4)`. -/
theorem integral_poly (n : ℕ) :
    (∫ u in (0:ℝ)..1, (1 - u) ^ 2 * u ^ (2 * n + 1))
      = 1 / (2 * (n : ℝ) + 2) - 2 / (2 * n + 3) + 1 / (2 * n + 4) := by
  have e : (fun u : ℝ ↦ (1 - u) ^ 2 * u ^ (2 * n + 1))
      = fun u ↦ u ^ (2 * n + 1) - 2 * u ^ (2 * n + 2) + u ^ (2 * n + 3) := by
    funext u; ring
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow]
  · push_cast; field_simp; ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- `∫_ε^b (1-u)² u^{2n+1} ≥ k(n) - ε²/2 - (1-b)`. -/
theorem integral_poly_ge (n : ℕ) {ε b : ℝ} (hε : 0 ≤ ε) (hεb : ε ≤ b) (hb : b ≤ 1) :
    1 / (2 * (n : ℝ) + 2) - 2 / (2 * n + 3) + 1 / (2 * n + 4) - ε ^ 2 / 2 - (1 - b)
      ≤ ∫ u in ε..b, (1 - u) ^ 2 * u ^ (2 * n + 1) := by
  have hc : Continuous (fun u : ℝ ↦ (1 - u) ^ 2 * u ^ (2 * n + 1)) := by fun_prop
  have hsplit : (∫ u in (0:ℝ)..1, (1 - u) ^ 2 * u ^ (2 * n + 1))
      = (∫ u in (0:ℝ)..ε, (1 - u) ^ 2 * u ^ (2 * n + 1)) + (∫ u in ε..b, (1 - u) ^ 2 * u ^ (2 * n + 1))
        + ∫ u in b..1, (1 - u) ^ 2 * u ^ (2 * n + 1) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  rw [integral_poly] at hsplit
  have h1 : (∫ u in (0:ℝ)..ε, (1 - u) ^ 2 * u ^ (2 * n + 1)) ≤ ε ^ 2 / 2 := by
    calc _ ≤ ∫ u in (0:ℝ)..ε, u := by
          refine intervalIntegral.integral_mono_on hε (hc.intervalIntegrable _ _)
            (continuous_id.intervalIntegrable _ _) fun u hu ↦ ?_
          have hu0 := hu.1
          have hu1 : u ≤ 1 := by linarith [hu.2]
          have h2 : (1 - u) ^ 2 ≤ 1 := by nlinarith
          have h3 : u ^ (2 * n + 1) ≤ u := by
            rw [pow_succ']; exact mul_le_of_le_one_right hu0 (pow_le_one₀ hu0 hu1)
          nlinarith [pow_nonneg hu0 (2 * n + 1), sq_nonneg (1 - u)]
      _ = ε ^ 2 / 2 := by simp [integral_id]
  have h2 : (∫ u in b..1, (1 - u) ^ 2 * u ^ (2 * n + 1)) ≤ 1 - b := by
    calc _ ≤ ∫ u in b..1, (1 : ℝ) := by
          refine intervalIntegral.integral_mono_on hb (hc.intervalIntegrable _ _)
            intervalIntegrable_const fun u hu ↦ ?_
          have hu0 : 0 ≤ u := by linarith [hu.1]
          have hu1 := hu.2
          have h2 : (1 - u) ^ 2 ≤ 1 := by nlinarith
          have h3 : u ^ (2 * n + 1) ≤ 1 := pow_le_one₀ hu0 hu1
          nlinarith [pow_nonneg hu0 (2 * n + 1), sq_nonneg (1 - u)]
      _ = 1 - b := by simp
  linarith

/-- An antiderivative of `u^m (-log u)`. -/
noncomputable def Alog (m : ℕ) (u : ℝ) : ℝ :=
  u ^ (m + 1) * (-Real.log u) / (m + 1) + u ^ (m + 1) / ((m : ℝ) + 1) ^ 2

theorem hasDerivAt_Alog (m : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (Alog m) (u ^ m * (-Real.log u)) u := by
  unfold Alog
  have h1 := hasDerivAt_pow (m + 1) u
  have h2 := (Real.hasDerivAt_log hu.ne').neg
  have := ((h1.mul h2).div_const ((m : ℝ) + 1)).add (h1.div_const (((m : ℝ) + 1) ^ 2))
  refine this.congr_deriv ?_
  simp only [Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem Alog_one (m : ℕ) : Alog m 1 = 1 / ((m : ℝ) + 1) ^ 2 := by
  simp [Alog]

/-- `∫_ε^b u(1-u)²(-log u) ≤ 13/144` and `∫_ε^b u³(1-u)(-log u) ≤ 9/400`, for `0 < ε ≤ 1/2`. -/
theorem integral_log_le {ε b : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hεb : ε ≤ b) (hb : b ≤ 1) :
    (∫ u in ε..b, u * (1 - u) ^ 2 * (-Real.log u)) ≤ 13 / 144 ∧
      (∫ u in ε..b, u ^ 3 * (1 - u) * (-Real.log u)) ≤ 9 / 400 := by
  have hlogε : 0 ≤ -Real.log ε := by
    have := Real.log_nonpos hε.le (by linarith); linarith
  have hcont1 : ContinuousOn (fun u : ℝ ↦ u * (1 - u) ^ 2 * (-Real.log u)) (Set.uIcc ε 1) := by
    intro u hu; rw [Set.uIcc_of_le (by linarith)] at hu
    have : u ≠ 0 := by linarith [hu.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hcont2 : ContinuousOn (fun u : ℝ ↦ u ^ 3 * (1 - u) * (-Real.log u)) (Set.uIcc ε 1) := by
    intro u hu; rw [Set.uIcc_of_le (by linarith)] at hu
    have : u ≠ 0 := by linarith [hu.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hnn1 : ∀ u ∈ Set.Icc ε 1, 0 ≤ u * (1 - u) ^ 2 * (-Real.log u) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have := Real.log_nonpos hu0.le hu.2
    exact mul_nonneg (mul_nonneg hu0.le (sq_nonneg _)) (by linarith)
  have hnn2 : ∀ u ∈ Set.Icc ε 1, 0 ≤ u ^ 3 * (1 - u) * (-Real.log u) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have := Real.log_nonpos hu0.le hu.2
    have h1 : 0 ≤ 1 - u := by linarith [hu.2]
    have h2 : 0 ≤ -Real.log u := by linarith
    exact mul_nonneg (mul_nonneg (pow_nonneg hu0.le 3) h1) h2
  have hmono : ∀ {h : ℝ → ℝ}, ContinuousOn h (Set.uIcc ε 1) → (∀ u ∈ Set.Icc ε 1, 0 ≤ h u) →
      (∫ u in ε..b, h u) ≤ ∫ u in ε..1, h u := by
    intro h hc hnn
    refine intervalIntegral.integral_mono_interval le_rfl hεb hb ?_ hc.intervalIntegrable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact hnn u ⟨hu.1.le, hu.2⟩
  have hderiv1 : ∀ u ∈ Set.uIcc ε 1, HasDerivAt (fun u ↦ Alog 1 u - 2 * Alog 2 u + Alog 3 u)
      (u * (1 - u) ^ 2 * (-Real.log u)) u := by
    intro u hu; rw [Set.uIcc_of_le (by linarith)] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    refine (((hasDerivAt_Alog 1 hu0).sub ((hasDerivAt_Alog 2 hu0).const_mul 2)).add
      (hasDerivAt_Alog 3 hu0)).congr_deriv ?_
    ring
  have hderiv2 : ∀ u ∈ Set.uIcc ε 1, HasDerivAt (fun u ↦ Alog 3 u - Alog 4 u)
      (u ^ 3 * (1 - u) * (-Real.log u)) u := by
    intro u hu; rw [Set.uIcc_of_le (by linarith)] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    refine ((hasDerivAt_Alog 3 hu0).sub (hasDerivAt_Alog 4 hu0)).congr_deriv ?_
    ring
  have hε1 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  constructor
  · refine (hmono hcont1 hnn1).trans ?_
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv1 hcont1.intervalIntegrable]
    simp only [Alog_one]
    have hA : 0 ≤ Alog 1 ε - 2 * Alog 2 ε + Alog 3 ε := by
      unfold Alog; push_cast
      have h1 : 0 ≤ ε ^ 2 * (-Real.log ε) / 2 - 2 * (ε ^ 3 * (-Real.log ε) / 3) := by
        have : ε ^ 3 ≤ ε ^ 2 / 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right this hlogε
        nlinarith
      have h2 : 0 ≤ ε ^ 2 / 4 - 2 * (ε ^ 3 / 9) := by nlinarith
      have h3 : 0 ≤ ε ^ 4 * (-Real.log ε) / 4 + ε ^ 4 / 16 := by positivity
      norm_num at h1 h2 h3 ⊢
      nlinarith
    norm_num
    linarith
  · refine (hmono hcont2 hnn2).trans ?_
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 hcont2.intervalIntegrable]
    simp only [Alog_one]
    have hA : 0 ≤ Alog 3 ε - Alog 4 ε := by
      unfold Alog; push_cast
      have h1 : ε ^ 5 * (-Real.log ε) / 5 ≤ ε ^ 4 * (-Real.log ε) / 4 := by
        have : ε ^ 5 ≤ ε ^ 4 := by nlinarith [pow_nonneg hε.le 4]
        have := mul_le_mul_of_nonneg_right this hlogε
        have : 0 ≤ ε ^ 4 * -Real.log ε := by positivity
        linarith
      have h2 : ε ^ 5 / 25 ≤ ε ^ 4 / 16 := by nlinarith [pow_nonneg hε.le 4]
      norm_num at h1 h2 ⊢
      linarith
    norm_num
    linarith

/-! ### Assembly -/

theorem continuousOn_Fweight {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContinuousOn Fweight (Set.Icc a b) := by
  intro u hu
  have h0 : 0 < u := by linarith [hu.1]
  have h1 : u < 1 := by linarith [hu.2]
  have hs := sin_pi_ne_zero h0 h1
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun v : ℝ ↦ Real.cot (Real.pi * v)) u := by
    simp only [Real.cot_eq_cos_div_sin]
    exact (by fun_prop : ContinuousAt (fun v : ℝ ↦ Real.cos (Real.pi * v)) u).div
      (by fun_prop) hs
  have e : Fweight = fun v ↦ 1 / Real.pi + (1 - v) * Real.cot (Real.pi * v) := by
    funext v; exact Fweight_eq v
  rw [e]
  exact continuousAt_const.add ((continuousAt_const.sub continuousAt_id).mul hc)

/-- The numerical constant `2 · (ζ(2)·13/144 + ζ(4)·9/400)`, halved: `C₂`. -/
noncomputable def C2hi : ℝ := Real.pi ^ 2 / 6 * (13 / 144) + Real.pi ^ 4 / 90 * (9 / 400)

/-- The partial sum defining the lower bound for `C₁`. -/
noncomputable def C1lo (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, cLow n * (1 / (2 * (n : ℝ) + 2) - 2 / (2 * n + 3) + 1 / (2 * n + 4))

set_option maxHeartbeats 2000000 in
/-- **`prop:tritura` on `[ε, b]`.** -/
theorem tritura (hcs : CotangentSeries.v1.cot_series_zeta_values) {ε b y : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hεb : ε ≤ b) (hb : b < 1) (hw : 0 ≤ y + Real.log ε) (N : ℕ) :
    2 * Real.pi * ∫ u in ε..b, Real.sqrt (Fweight u ^ 2 + (1 - u) ^ 2) * (y + Real.log u)
      ≤ y ^ 2 - (y + Real.log ε) ^ 2 - 2 * C1lo N * (y + 1) + 2 * C2hi
        + (2 * (y + 1) * (ε ^ 2 / 2 + (1 - b)) * ∑ n ∈ Finset.range N, cLow n
          + Real.pi ^ 2 * gT b * y) := by
  have hπ := Real.pi_pos
  have hb0 : 0 < b := by linarith
  set W : ℝ → ℝ := fun u ↦ y + Real.log u with hW
  have hmem : ∀ u ∈ Set.uIcc ε b, 0 < u ∧ u < 1 ∧ 0 ≤ W u ∧ W u ≤ y := by
    intro u hu
    rw [Set.uIcc_of_le hεb] at hu
    have h0 : 0 < u := by linarith [hu.1]
    refine ⟨h0, by linarith [hu.2], ?_, ?_⟩
    · have := Real.log_le_log hε hu.1; simp only [hW]; linarith
    · have := Real.log_nonpos h0.le (by linarith [hu.2]); simp only [hW]; linarith
  have hεmem : ε ∈ Set.uIcc ε b := by rw [Set.uIcc_of_le hεb]; exact ⟨le_rfl, hεb⟩
  have hbmem : b ∈ Set.uIcc ε b := by rw [Set.uIcc_of_le hεb]; exact ⟨hεb, le_rfl⟩
  have hy : 0 ≤ y := by have := (hmem ε hεmem).2.2.2; linarith [(hmem ε hεmem).2.2.1]
  -- continuity on the interval
  have hIcc : Set.uIcc ε b = Set.Icc ε b := Set.uIcc_of_le hεb
  have hlogc : ContinuousOn Real.log (Set.Icc ε b) := fun u hu ↦
    (Real.continuousAt_log (by linarith [hu.1])).continuousWithinAt
  have hWc : ContinuousOn W (Set.Icc ε b) := continuousOn_const.add hlogc
  have hFc := continuousOn_Fweight hε hb
  have hgc := continuousOn_gT hε hb
  set g' : ℝ → ℝ := fun u ↦ Fweight u ^ 2 + (1 - u) ^ 2 - 1 / (Real.pi * u) ^ 2 with hg'
  have hinvc : ContinuousOn (fun u : ℝ ↦ 1 / (Real.pi * u)) (Set.Icc ε b) := fun u hu ↦
    (continuousAt_const.div (by fun_prop) (by have : 0 < u := by linarith [hu.1]
                                              positivity)).continuousWithinAt
  have hg'c : ContinuousOn g' (Set.Icc ε b) :=
    ((hFc.pow 2).add (((continuousOn_const (c := (1:ℝ))).sub continuousOn_id).pow 2)).sub
      (hinvc.pow 2) |>.congr (fun u _ ↦ by simp [hg']; ring)
  -- step 1: the tangent-line bound
  have hstep1 : (∫ u in ε..b, Real.sqrt (Fweight u ^ 2 + (1 - u) ^ 2) * W u)
      ≤ ∫ u in ε..b, (W u / (Real.pi * u) + (Real.pi / 2) * (u * W u * g' u)) := by
    refine intervalIntegral.integral_mono_on hεb ?_ ?_ fun u hu ↦ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]
      exact (((hFc.pow 2).add ((continuousOn_const.sub continuousOn_id).pow 2)).sqrt).mul hWc
    · refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]
      refine (hWc.mul hinvc |>.congr (fun u _ ↦ by simp [div_eq_mul_inv])).add
        (continuousOn_const.mul ((continuousOn_id.mul hWc).mul hg'c))
    · obtain ⟨h0, h1, hW0, -⟩ := hmem u (by rw [hIcc]; exact hu)
      have hA : 0 < 1 / (Real.pi * u) := by positivity
      have ht := sqrt_le_tangent hA (by positivity : 0 ≤ Fweight u ^ 2 + (1 - u) ^ 2)
      have e : 1 / (Real.pi * u) + (Fweight u ^ 2 + (1 - u) ^ 2 - (1 / (Real.pi * u)) ^ 2)
          / (2 * (1 / (Real.pi * u))) = 1 / (Real.pi * u) + (Real.pi / 2) * (u * g' u) := by
        simp only [hg', div_pow]; field_simp
      rw [e] at ht
      have := mul_le_mul_of_nonneg_right ht hW0
      calc _ ≤ (1 / (Real.pi * u) + Real.pi / 2 * (u * g' u)) * W u := this
        _ = _ := by field_simp
  -- step 2: `∫ W/(πu)`
  have hstep2 : (∫ u in ε..b, W u / (Real.pi * u)) = (W b ^ 2 - W ε ^ 2) / (2 * Real.pi) := by
    have hd : ∀ u ∈ Set.uIcc ε b, HasDerivAt (fun u ↦ W u ^ 2 / (2 * Real.pi))
        (W u / (Real.pi * u)) u := by
      intro u hu
      have h0 := (hmem u hu).1
      have := (((hasDerivAt_const u y).add (Real.hasDerivAt_log h0.ne')).pow 2).div_const
        (2 * Real.pi)
      refine this.congr_deriv ?_
      simp only [hW, Pi.add_apply]; push_cast; field_simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
    · ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]; exact hWc.mul hinvc |>.congr (fun u _ ↦ by simp [div_eq_mul_inv])
  -- step 3: integration by parts
  have hstep3 : (∫ u in ε..b, (u * W u) * g' u)
      = (b * W b) * gT b - (ε * W ε) * gT ε - ∫ u in ε..b, (W u + 1) * gT u := by
    have hd1 : ∀ u ∈ Set.uIcc ε b, HasDerivAt (fun u ↦ u * W u) (W u + 1) u := by
      intro u hu
      have h0 := (hmem u hu).1
      refine ((hasDerivAt_id u).mul ((hasDerivAt_const u y).add
        (Real.hasDerivAt_log h0.ne'))).congr_deriv ?_
      simp only [hW, id, Pi.add_apply]; field_simp; ring
    have hd2 : ∀ u ∈ Set.uIcc ε b, HasDerivAt gT (g' u) u := fun u hu ↦
      hasDerivAt_gT (hmem u hu).1 (hmem u hu).2.1
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hd1 hd2
      ((hWc.add continuousOn_const).intervalIntegrable_of_Icc hεb)
      (hg'c.intervalIntegrable_of_Icc hεb)
  -- step 5: the lower bound on `∫ (W+1) g`
  have hgb : 0 ≤ gT b := gT_nonneg hcs hb0 hb
  have hgε : 0 ≤ gT ε := gT_nonneg hcs hε (by linarith)
  have hint_g : (2 / Real.pi ^ 2) * ∑ n ∈ Finset.range N,
      cLow n * (1 / (2 * (n : ℝ) + 2) - 2 / (2 * n + 3) + 1 / (2 * n + 4) - ε ^ 2 / 2 - (1 - b))
      ≤ ∫ u in ε..b, gT u := by
    calc _ ≤ ∫ u in ε..b, (2 / Real.pi ^ 2) * ∑ n ∈ Finset.range N,
            cLow n * ((1 - u) ^ 2 * u ^ (2 * n + 1)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum
            (fun n _ ↦ (Continuous.intervalIntegrable (by fun_prop) _ _))]
          gcongr with n
          rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_poly_ge n hε.le hεb hb.le) (cLow_nonneg n)
      _ ≤ ∫ u in ε..b, gT u := by
          refine intervalIntegral.integral_mono_on hεb (Continuous.intervalIntegrable (by fun_prop) _ _)
            (hgc.intervalIntegrable_of_Icc hεb) fun u hu ↦ ?_
          obtain ⟨h0, h1, -, -⟩ := hmem u (by rw [hIcc]; exact hu)
          have hf := freal_ge_partial hcs h0 h1 N
          unfold gT
          rw [le_div_iff₀ hπ]
          have e : (2 / Real.pi ^ 2) * (∑ n ∈ Finset.range N, cLow n * ((1 - u) ^ 2 * u ^ (2 * n + 1)))
              * Real.pi = (1 - u) ^ 2 * ((2 / Real.pi) * ∑ n ∈ Finset.range N, cLow n * u ^ (2 * n + 1)) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun n _ ↦ by field_simp
          rw [e]
          exact mul_le_mul_of_nonneg_left hf (sq_nonneg _)
  have hint_log : -(2 / Real.pi ^ 2) * (Real.pi ^ 2 / 6 * (13 / 144) + Real.pi ^ 4 / 90 * (9 / 400))
      ≤ ∫ u in ε..b, Real.log u * gT u := by
    obtain ⟨hl1, hl2⟩ := integral_log_le hε hε2 hεb hb.le
    have hcont1 : Continuous (fun u : ℝ ↦ u * (1 - u) ^ 2) := by fun_prop
    have hi1 : IntervalIntegrable (fun u : ℝ ↦ u * (1 - u) ^ 2 * (-Real.log u)) MeasureTheory.volume ε b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]; exact (hcont1.continuousOn.mul hlogc.neg)
    have hi2 : IntervalIntegrable (fun u : ℝ ↦ u ^ 3 * (1 - u) * (-Real.log u)) MeasureTheory.volume ε b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]; exact ((by fun_prop : Continuous fun u : ℝ ↦ u ^ 3 * (1 - u)).continuousOn.mul hlogc.neg)
    have hup : (∫ u in ε..b, -(Real.log u * gT u))
        ≤ ∫ u in ε..b, (2 / Real.pi ^ 2) * (Real.pi ^ 2 / 6 * (u * (1 - u) ^ 2 * (-Real.log u))
            + Real.pi ^ 4 / 90 * (u ^ 3 * (1 - u) * (-Real.log u))) := by
      refine intervalIntegral.integral_mono_on hεb ?_ ((hi1.const_mul _).add (hi2.const_mul _) |>.const_mul _)
        fun u hu ↦ ?_
      · exact ((hlogc.mul hgc).neg).intervalIntegrable_of_Icc hεb
      · obtain ⟨h0, h1, -, -⟩ := hmem u (by rw [hIcc]; exact hu)
        have hf := freal_le hcs h0 h1
        have hlog : 0 ≤ -Real.log u := by have := Real.log_nonpos h0.le h1.le; linarith
        have hq : (1 - u) ^ 2 * (u ^ 3 / (1 - u ^ 2)) ≤ u ^ 3 * (1 - u) := by
          have h1u : 0 < 1 + u := by linarith
          have e : (1 - u) ^ 2 * (u ^ 3 / (1 - u ^ 2)) = u ^ 3 * (1 - u) / (1 + u) := by
            have : 1 - u ^ 2 = (1 - u) * (1 + u) := by ring
            rw [this]; field_simp [show (1 - u) ≠ 0 by linarith]
          rw [e, div_le_iff₀ h1u]
          have : 0 ≤ u ^ 3 * (1 - u) := by have : 0 ≤ 1 - u := by linarith
                                           positivity
          nlinarith
        have hg : gT u ≤ (2 / Real.pi ^ 2) * (Real.pi ^ 2 / 6 * (u * (1 - u) ^ 2)
            + Real.pi ^ 4 / 90 * (u ^ 3 * (1 - u))) := by
          unfold gT
          rw [div_le_iff₀ hπ]
          calc (1 - u) ^ 2 * freal u
              ≤ (1 - u) ^ 2 * ((2 / Real.pi) * (Real.pi ^ 2 / 6 * u
                  + Real.pi ^ 4 / 90 * (u ^ 3 / (1 - u ^ 2)))) :=
                mul_le_mul_of_nonneg_left hf (sq_nonneg _)
            _ = (2 / Real.pi) * (Real.pi ^ 2 / 6 * (u * (1 - u) ^ 2)
                  + Real.pi ^ 4 / 90 * ((1 - u) ^ 2 * (u ^ 3 / (1 - u ^ 2)))) := by ring
            _ ≤ (2 / Real.pi) * (Real.pi ^ 2 / 6 * (u * (1 - u) ^ 2)
                  + Real.pi ^ 4 / 90 * (u ^ 3 * (1 - u))) := by gcongr
            _ = _ := by field_simp
        calc -(Real.log u * gT u) = gT u * (-Real.log u) := by ring
          _ ≤ (2 / Real.pi ^ 2) * (Real.pi ^ 2 / 6 * (u * (1 - u) ^ 2)
              + Real.pi ^ 4 / 90 * (u ^ 3 * (1 - u))) * (-Real.log u) :=
            mul_le_mul_of_nonneg_right hg hlog
          _ = _ := by ring
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hup
    have hk : 0 ≤ 2 / Real.pi ^ 2 := by positivity
    have : (2 / Real.pi ^ 2) * (Real.pi ^ 2 / 6 * (∫ u in ε..b, u * (1 - u) ^ 2 * (-Real.log u))
        + Real.pi ^ 4 / 90 * ∫ u in ε..b, u ^ 3 * (1 - u) * (-Real.log u))
        ≤ (2 / Real.pi ^ 2) * (Real.pi ^ 2 / 6 * (13 / 144) + Real.pi ^ 4 / 90 * (9 / 400)) := by
      gcongr
    linarith
  have hsplit : (∫ u in ε..b, (W u + 1) * gT u)
      = (y + 1) * (∫ u in ε..b, gT u) + ∫ u in ε..b, Real.log u * gT u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun u _ ↦ by simp only [hW]; ring
    · exact (hgc.intervalIntegrable_of_Icc hεb).const_mul _
    · exact (hlogc.mul hgc).intervalIntegrable_of_Icc hεb
  -- assemble
  have hRHS : (∫ u in ε..b, (W u / (Real.pi * u) + (Real.pi / 2) * (u * W u * g' u)))
      = (∫ u in ε..b, W u / (Real.pi * u)) + (Real.pi / 2) * ∫ u in ε..b, (u * W u) * g' u := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
    · refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]; exact hWc.mul hinvc |>.congr (fun u _ ↦ by simp [div_eq_mul_inv])
    · exact ((continuousOn_id.mul hWc).mul hg'c |>.const_mul _ |>.intervalIntegrable_of_Icc hεb)
  rw [hRHS, hstep2, hstep3, hsplit] at hstep1
  obtain ⟨-, -, hWb0, hWby⟩ := hmem b hbmem
  obtain ⟨-, -, hWε0, -⟩ := hmem ε hεmem
  have hWb2 : W b ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hWb0 hWby 2
  have hbW : b * W b * gT b ≤ gT b * y := by
    have : b * W b ≤ y := by nlinarith
    nlinarith
  have hεW : 0 ≤ ε * W ε * gT ε := by positivity
  have hsum_expand : (2 / Real.pi ^ 2) * ∑ n ∈ Finset.range N,
      cLow n * (1 / (2 * (n : ℝ) + 2) - 2 / (2 * n + 3) + 1 / (2 * n + 4) - ε ^ 2 / 2 - (1 - b))
      = (2 / Real.pi ^ 2) * (C1lo N - (ε ^ 2 / 2 + (1 - b)) * ∑ n ∈ Finset.range N, cLow n) := by
    rw [C1lo, mul_comm (ε ^ 2 / 2 + (1 - b)), Finset.sum_mul, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  rw [hsum_expand] at hint_g
  have hy1 : 0 ≤ y + 1 := by linarith
  have hfin := mul_le_mul_of_nonneg_left hint_g hy1
  simp only [hW] at hstep1 hWb2 hbW
  unfold C2hi
  have hπ2 : Real.pi ^ 2 ≠ 0 := by positivity
  have key : 2 * Real.pi * ((W b ^ 2 - W ε ^ 2) / (2 * Real.pi)
      + Real.pi / 2 * (b * W b * gT b - ε * W ε * gT ε
        - ((y + 1) * (∫ u in ε..b, gT u) + ∫ u in ε..b, Real.log u * gT u)))
      = W b ^ 2 - W ε ^ 2 + Real.pi ^ 2 * (b * W b * gT b - ε * W ε * gT ε)
        - Real.pi ^ 2 * ((y + 1) * (∫ u in ε..b, gT u)) - Real.pi ^ 2 * ∫ u in ε..b, Real.log u * gT u := by
    field_simp; ring
  simp only [hW] at key
  have h1 := mul_le_mul_of_nonneg_left hstep1 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  have e1 : Real.pi ^ 2 * ((y + 1) * ((2 / Real.pi ^ 2) *
      (C1lo N - (ε ^ 2 / 2 + (1 - b)) * ∑ n ∈ Finset.range N, cLow n)))
      = 2 * (y + 1) * (C1lo N - (ε ^ 2 / 2 + (1 - b)) * ∑ n ∈ Finset.range N, cLow n) := by
    field_simp
  have e2 : Real.pi ^ 2 * (-(2 / Real.pi ^ 2) * (Real.pi ^ 2 / 6 * (13 / 144) + Real.pi ^ 4 / 90 * (9 / 400)))
      = -(2 * (Real.pi ^ 2 / 6 * (13 / 144) + Real.pi ^ 4 / 90 * (9 / 400))) := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hfin (by positivity : (0:ℝ) ≤ Real.pi ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hint_log (by positivity : (0:ℝ) ≤ Real.pi ^ 2)
  rw [e2] at h3
  have h4 : Real.pi ^ 2 * (b * (y + Real.log b) * gT b) ≤ Real.pi ^ 2 * (gT b * y) :=
    mul_le_mul_of_nonneg_left hbW (by positivity)
  have h5 : 0 ≤ Real.pi ^ 2 * (ε * (y + Real.log ε) * gT ε) := by positivity
  rw [key] at h1
  rw [e1] at h2
  linarith [h1, h2, h3, h4, h5, hWb2]

/-! ### The numbers -/

theorem C1lo_twelve : (0.1672 : ℝ) ≤ C1lo 12 := by
  have hπ := Real.pi_gt_d6
  have h2 : (9.869600 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have h4 : (97.409 : ℝ) ≤ Real.pi ^ 4 := by nlinarith
  simp only [C1lo, Finset.sum_range_succ, Finset.sum_range_zero, cLow]
  norm_num
  nlinarith

theorem C2hi_le : C2hi ≤ 0.1729 := by
  have hπ := Real.pi_lt_d6
  have hπ0 := Real.pi_pos
  have h2 : Real.pi ^ 2 ≤ 9.869607 := by nlinarith
  have h4 : Real.pi ^ 4 ≤ 97.4092 := by nlinarith
  unfold C2hi
  nlinarith

theorem sum_cLow_twelve : ∑ n ∈ Finset.range 12, cLow n ≤ 14 := by
  have hπ := Real.pi_lt_d6
  have hπ0 := Real.pi_pos
  have h2 : Real.pi ^ 2 ≤ 9.869607 := by nlinarith
  have h4 : Real.pi ^ 4 ≤ 97.4092 := by nlinarith
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cLow]
  norm_num
  nlinarith

/-- `g(b) ≤ (1-b)²/(π² b) + (1-b)/π²`, from `cot(πb) ≥ -1/(π(1-b))`. -/
theorem gT_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1) :
    gT b ≤ (1 - b) ^ 2 / (Real.pi ^ 2 * b) + (1 - b) / Real.pi ^ 2 := by
  have hπ := Real.pi_pos
  have h1b : 0 < 1 - b := by linarith
  have hcot : -(1 / (Real.pi * (1 - b))) ≤ Real.cot (Real.pi * b) := by
    have hlt := cot_lt_inv (u := Real.pi * (1 - b)) (by positivity) (by nlinarith)
    rw [show Real.pi * (1 - b) = Real.pi - Real.pi * b by ring, cot_pi_sub] at hlt
    rw [show Real.pi * (1 - b) = Real.pi - Real.pi * b by ring]
    linarith
  have hf : freal b ≤ 1 / (Real.pi * b) + 1 / (Real.pi * (1 - b)) := by
    unfold freal; linarith
  unfold gT
  calc (1 - b) ^ 2 * freal b / Real.pi
      ≤ (1 - b) ^ 2 * (1 / (Real.pi * b) + 1 / (Real.pi * (1 - b))) / Real.pi := by gcongr
    _ = (1 - b) ^ 2 / (Real.pi ^ 2 * b) + (1 - b) / Real.pi ^ 2 := by
        field_simp

end CH2Section7T
