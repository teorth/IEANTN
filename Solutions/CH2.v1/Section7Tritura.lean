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

end CH2Section7T
