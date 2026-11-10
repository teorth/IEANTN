import RSBounds.QuarticHead1000BudgetNumerics
import RSBounds.QuarticLowZeroBounds
import RSBounds.QuarticFirst29BudgetApplication
import RSBounds.Head1000Table

/-!
# The quartic b = 23 low-zero bound with the 649-zero head

The same argument as `QuarticLowZeroBounds`, with the explicit head at height
1000 instead of 100: the head sum and the count come from `Head1000`, under
its hypothesis `Head1000.Certified`, and the generic window and Rosser
estimates are applied with `D = 1000`. delta, the eight cancellation bands and
the high-zero term are unchanged.
-/

open Complex
open scoped BigOperators

namespace TernaryGoldbach.RSBounds.QuarticHead1000Budget
open BacklundCountIdentity WeightedZetaZeros
open QuarticFirst29BudgetNumerics QuarticFirst29BudgetBridges QuarticHead1000BudgetNumerics

private theorem majorant_delta_eq : PolynomialZeroMajorants.delta = (delta : ℝ) := by
  norm_num [PolynomialZeroMajorants.delta, delta]

theorem thousand_le_Y : (1000 : ℝ) ≤ (Y : ℝ) := by norm_num [Y, delta]

theorem thousand_le_cutoff_zero : (1000 : ℝ) ≤ (cutoff 0 : ℝ) := by
  norm_num [cutoff, Y, delta]

theorem lowIntegral1000_eq : lowIntegral1000 = RosserWeightedBounds.I 1000 (Y : ℝ) := by
  unfold lowIntegral1000 RosserWeightedBounds.I
  ring

theorem lineWeight1000_eq :
    lineWeight1000 =
      (a : ℝ) * (2.028658 + RosserWeightedBounds.I 1000 (Y : ℝ) +
        (RosserWeightedBounds.G 1000 - 649) / 1000) +
      (C : ℝ) * RosserTailIntegrals.J (Y : ℝ) +
      2 * rosserR 1.588 (Y : ℝ) * ((C : ℝ) / (Y : ℝ) ^ 5 - (a : ℝ) / (Y : ℝ)) := by
  simp only [lineWeight1000, F_eq_rosserF, R_eq_rosserR, fifthTail_eq_J,
    lowIntegral1000_eq, RosserWeightedBounds.G]

/-- The 649-zero head and the joined reciprocal/fifth-power estimate produce
the line weight. -/
theorem head_and_tail_le_lineWeight1000 (h : Head1000.Certified) :
    (a : ℝ) * (∑ ρ ∈ closedPositiveZeros 1000,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) +
      (a : ℝ) * weightedSum 1000 (Y : ℝ) (fun t => 1 / t) +
      (C : ℝ) * weightedSum (Y : ℝ) (A : ℝ) (fun t => 1 / t ^ 5) ≤ lineWeight1000 := by
  have hh := mul_le_mul_of_nonneg_left (Head1000.weighted_head_le h) a_nonneg
  have ht := RosserWeightedSplit.reciprocal_fifth_split_le
    (D := 1000) (Y := (Y : ℝ)) (T := (A : ℝ)) (k := (a : ℝ)) (C := (C : ℝ))
    (by norm_num) thousand_le_Y Y_le_A a_nonneg C_nonneg split_coefficient_le
  rw [Head1000.positiveZeroCount_thousand h] at ht
  rw [lineWeight1000_eq]
  nlinarith only [hh, ht]

/-- Actual low-zero contribution, counting multiplicity, for either quartic
smoothing. -/
theorem positive_low_sum_le (h : Head1000.Certified) (lower : Bool) {x : ℝ} (hx : 0 < x)
    (hRH : Goals.FiniteRH 1894438.5122) :
    (∑ ρ ∈ closedPositiveZeros (A : ℝ),
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
        ‖PolynomialZeroMajorants.coefficient lower x ρ‖) ≤
      Real.sqrt x * (lineWeight1000 - ((a : ℝ) - 0.931) * bandMass) := by
  have hgeneric := ZeroWindowFiniteSum.sum_le_windows
    (D := 1000) (L := (cutoff 0 : ℝ)) (U := (cutoff 8 : ℝ))
    (Y := (Y : ℝ)) (A := (A : ℝ)) (s := Real.sqrt x)
    (k := (a : ℝ)) (C := (C : ℝ)) (r := 0.931)
    (by norm_num) thousand_le_cutoff_zero (cutoff_monotone (by norm_num : 0 ≤ 8))
    cutoff_eight_le_Y Y_le_A (Real.sqrt_nonneg _) a_nonneg
    (fun ρ => ‖PolynomialZeroMajorants.coefficient lower x ρ‖)
    (by
      intro ρ hρ
      have h := PolynomialZeroMajorants.norm_coefficient_le_low lower hx
        (QuarticLowZeroBounds.low_zero_re hRH hρ)
      rw [majorant_delta_eq, ← a_cast_eq] at h
      exact h)
    (by
      intro ρ hρ _
      have him := ((mem_closedPositiveZeros_iff (by norm_num [A])).mp hρ).2.1
      have h := PolynomialZeroMajorants.norm_coefficient_le_high_line lower hx
        (QuarticLowZeroBounds.low_zero_re hRH hρ) him.ne'
      rw [abs_of_pos him, majorant_delta_eq, ← C_cast_eq_R4] at h
      exact h)
    (by
      intro ρ hρ hlo hhi
      apply PolynomialZeroMajorants.norm_coefficient_le_band_pos lower hx
        (QuarticLowZeroBounds.low_zero_re hRH hρ)
      · rw [majorant_delta_eq, ← cutoff_zero_eq]
        exact hlo.le
      · rwa [majorant_delta_eq, ← cutoff_eight_eq])
  change (∑ ρ ∈ closedPositiveZeros (A : ℝ),
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
      ‖PolynomialZeroMajorants.coefficient lower x ρ‖) ≤ _ at hgeneric
  apply hgeneric.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hb := mul_le_mul_of_nonneg_left QuarticLowZeroBounds.bandMass_le_reciprocal saving_nonneg
  have hh := head_and_tail_le_lineWeight1000 h
  change (a : ℝ) * (∑ ρ ∈ closedPositiveZeros 1000,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) +
      (a : ℝ) * weightedSum 1000 (Y : ℝ) (fun t => 1 / t) +
      (C : ℝ) * weightedSum (Y : ℝ) (A : ℝ) (fun t => 1 / t ^ 5) -
      ((a : ℝ) - 0.931) * weightedSum (cutoff 0 : ℝ) (cutoff 8 : ℝ) (fun t => 1 / t) ≤ _
  linarith

/-- The full scalar expression is below the 1976 target for every x ≥ e^23. -/
theorem relativeBudget1000_lt {x : ℝ} (hx : Real.exp 23 ≤ x) :
    2 * (delta : ℝ) + highWeight + sqrtCoefficient1000 / Real.sqrt x +
      (highWeight + Real.log (2 * Real.pi) + 0.1) / x < 0.00020171 := by
  have hq : sqrtCoefficient1000 / Real.sqrt x ≤ sqrtCoefficient1000 / 98715 :=
    div_le_div_of_nonneg_left sqrtCoefficient1000_pos.le (by norm_num)
      (QuarticFirst29BudgetApplication.sqrt_lower hx)
  have hk : (highWeight + Real.log (2 * Real.pi) + 0.1) / x ≤
      (highWeight + Real.log (2 * Real.pi) + 0.1) / (98715 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left QuarticFirst29BudgetApplication.constant_term_pos.le
      (by norm_num) (QuarticFirst29BudgetApplication.x_lower hx)
  have hb := scalarBudget1000_lt
  unfold scalarBudget1000 at hb
  linarith

end TernaryGoldbach.RSBounds.QuarticHead1000Budget
