import RSBounds.QuarticHead1000Budget
import RSBounds.RosserSchoenfeld1975

/-!
# The 1976 b = 23 row from the 649-zero head

`Goals.PsiTable1976` (Schoenfeld 1976, b = 23: `|ψ(x) - x| < 0.00020171 x` for
`x ≥ e^23`, under finite RH through 1894438.5122), proved from the hypothesis
`Head1000.Certified`: the statements of `Zeros0to1000` (`located`, `unique`,
`count`) of `Garald1/zeta-zero-locations`. The argument is that of
`RosserSchoenfeld1975.lean` (degree-four smoothing, delta = 0.0000211, eight
cancellation bands, the unconditional high-zero bound), with the explicit zero
head at height 1000 (649 zeros) instead of 100 (29 zeros).

Until the proof of `Zeros0to1000` is available in this project, the result is
conditional on `Head1000.Certified`.
-/

open Complex Finset Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.QuarticHead1000ZeroSumBound

open TernaryGoldbach.Explicit BacklundCountIdentity QuarticFirst29BudgetNumerics
  QuarticHead1000BudgetNumerics

theorem norm_low_sum_le (h : Head1000.Certified) (lower : Bool) {x T : ℝ} (hx : 0 < x)
    (hRH : Goals.FiniteRH 1894438.5122) (hAT : (A : ℝ) < T) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ (A : ℝ)),
      (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
      Real.sqrt x * sqrtCoefficient1000 := by
  have hA : (0 : ℝ) < (A : ℝ) := by norm_num [A]
  have hh := PolynomialZeroPairing.norm_low_sum_le_two_closed hA hAT
    (PolynomialZeroMajorants.coefficient lower x)
    (fun ρ _ => PolynomialZeroMajorants.norm_coefficient_conj lower hx ρ)
  have hp := QuarticHead1000Budget.positive_low_sum_le h lower hx hRH
  calc
    _ ≤ 2 * (Real.sqrt x * (lineWeight1000 - ((a : ℝ) - 0.931) * bandMass)) :=
      hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ = Real.sqrt x * sqrtCoefficient1000 := by unfold sqrtCoefficient1000; ring

/-- The actual finite complex sum, with every analytic multiplicity retained. -/
theorem norm_sum_le (h : Head1000.Certified) (lower : Bool) {x T : ℝ} (hx : 1 ≤ x)
    (hRH : Goals.FiniteRH 1894438.5122) (hAT : (A : ℝ) < T) (hg : zetaGoodHeight T) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
      Real.sqrt x * sqrtCoefficient1000 + (x + 1) * highWeight := by
  classical
  have hlo := norm_low_sum_le h lower (by linarith : 0 < x) hRH hAT
  have hhi := QuarticHighZeroBounds.norm_high_sum_le lower hx hAT hg
  rw [← Finset.sum_filter_add_sum_filter_not (zerosRectD zetaF T)
    (fun ρ => |ρ.im| ≤ (A : ℝ))]
  simp only [not_le]
  exact (norm_add_le _ _).trans (add_le_add hlo hhi)

/-- The normalized budget used by the psi reduction. -/
theorem norm_sum_le_budget (h : Head1000.Certified) (lower : Bool) {x T : ℝ} (hx : 1 ≤ x)
    (hRH : Goals.FiniteRH 1894438.5122) (hAT : (A : ℝ) < T) (hg : zetaGoodHeight T) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
      x * (highWeight + sqrtCoefficient1000 / Real.sqrt x + highWeight / x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  have hdiv : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hs0).mpr
    nlinarith [Real.sq_sqrt hx0.le]
  calc
    _ ≤ Real.sqrt x * sqrtCoefficient1000 + (x + 1) * highWeight :=
      norm_sum_le h lower hx hRH hAT hg
    _ = x * highWeight + (x / Real.sqrt x) * sqrtCoefficient1000 + highWeight := by
      rw [hdiv]
      ring
    _ = _ := by
      field_simp [hx0.ne', hs0]

end TernaryGoldbach.RSBounds.QuarticHead1000ZeroSumBound

namespace TernaryGoldbach.RSBounds.PsiTable1976

open TernaryGoldbach.Explicit PolynomialExplicit QuarticFirst29BudgetNumerics
  QuarticHead1000BudgetNumerics

/-- The 1976 b = 23 estimate, given the `Zeros0to1000` statements. -/
theorem psi_error_lt (h : Head1000.Certified) (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ}
    (hx : Real.exp 23 ≤ x) : |Chebyshev.psi x - x| < 0.00020171 * x := by
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  have hx1 : 1 ≤ x := by nlinarith [QuarticFirst29BudgetApplication.x_lower hx]
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  have hlarge : ∀ᶠ k : ℕ in atTop, (A : ℝ) < T k := by
    filter_upwards [eventually_ge_atTop (1894439 : ℕ)] with k hk
    have hkR : (1894439 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have ht := (hT.mem k).1
    have hA' : (A : ℝ) < 1894439 := by norm_num [A]
    linarith
  let zeroBudget : ℝ := highWeight + sqrtCoefficient1000 / Real.sqrt x + highWeight / x
  have hnorm (lower : Bool) : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
          x * zeroBudget := by
    filter_upwards [hlarge] with k hk
    exact QuarticHead1000ZeroSumBound.norm_sum_le_budget h lower hx1 hRH hk
      (PolynomialZeroCountBridge.zetaGoodHeight_of_goodHeights hT k)
  have hpsi := PolynomialPsiFromZeroSums.psi_error_of_eventually_bounded_zero_sums
    hT hx
    (by simpa [PolynomialZeroMajorants.coefficient, PolynomialZeroMajorants.delta] using hnorm false)
    (by simpa [PolynomialZeroMajorants.coefficient, PolynomialZeroMajorants.delta] using hnorm true)
  have hrelative : |Chebyshev.psi x - x| / x < 0.00020171 := by
    calc
      _ ≤ 2 * (0.0000211 : ℝ) + (Real.log (2 * Real.pi) + 0.1) / x + zeroBudget := hpsi
      _ = 2 * (delta : ℝ) + highWeight + sqrtCoefficient1000 / Real.sqrt x +
          (highWeight + Real.log (2 * Real.pi) + 0.1) / x := by
        rw [QuarticFirst29BudgetBridges.delta_cast_eq]
        dsimp only [zeroBudget]
        ring
      _ < 0.00020171 := QuarticHead1000Budget.relativeBudget1000_lt hx
  exact (div_lt_iff₀ hx0).mp hrelative

/-- The 1976 b = 23 row, conditional on the `Zeros0to1000` statements. Once
those are proved in this project, `Goals.PsiTable1976` holds under finite RH
through 1894438.5122 alone. -/
theorem of_certified (h : Head1000.Certified) : Goals.PsiTable1976 := by
  intro hRH x hx
  exact psi_error_lt h hRH hx

/-- `psi_error_lt` with the three statements `located`, `unique`, `count` of
`Zeros0to1000` as separate hypotheses, in their exact form. These are the
statements compared by `comparator-psi1976-conditional.json`. (A `def` such as
`Head1000.Certified` cannot be compared from a one-file challenge here: its
literals carry auxiliary proof constants whose names depend on the other
definitions elaborated earlier in the same file. Theorem types carry those
proofs inline.) -/
theorem psi_error_of_zeros0to1000
    (located : ∀ s ∈ Zeros0to1000.zerosBetween 0 1000, s.re = 1 / 2 ∧
      analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros0to1000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)
    (unique : ∀ m ∈ Zeros0to1000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)
    (count : (Zeros0to1000.zerosBetween 0 1000).ncard = 649)
    (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x) :
    |Chebyshev.psi x - x| < 0.00020171 * x :=
  psi_error_lt ⟨located, unique, count⟩ hRH hx

/-- `of_certified` with the three statements of `Zeros0to1000` as separate
hypotheses. -/
theorem of_zeros0to1000
    (located : ∀ s ∈ Zeros0to1000.zerosBetween 0 1000, s.re = 1 / 2 ∧
      analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros0to1000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)
    (unique : ∀ m ∈ Zeros0to1000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)
    (count : (Zeros0to1000.zerosBetween 0 1000).ncard = 649) :
    Goals.PsiTable1976 :=
  of_certified ⟨located, unique, count⟩

end TernaryGoldbach.RSBounds.PsiTable1976
