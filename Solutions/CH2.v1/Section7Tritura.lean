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

end CH2Section7T
