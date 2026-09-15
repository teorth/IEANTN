/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section6Hyp

/-!
# Section 7: sums over zeros by Stieltjes integration (`lem:Lehmanmodern`)

For `φ` decreasing, non-negative and `C¹` on `[t₀, t₁]` with `t₀ ≥ 1`,

`∑_{t₀ < γ ≤ t₁} φ(γ) ≤ ∫_{t₀}^{t₁} φ(t) (log(t/2π)/(2π) + 1/(5t)) dt + φ(t₀)(log t₀/5 + 2 - Q(t₀))`

where `Q = N - M` is the Riemann–von Mangoldt remainder, bounded by `ZeroCount.v1.rvm_error_bound`.
This is eq. `seguitor` of Chirre–Helfgott, with `(1/5)∫φ/t` and the main term merged.

The proof never integrates against `Q` itself, which is a step function: the count `N(t) - N(t₀)`
is bounded by the smooth `G(t) = M(t) + log t/5 + 2 - N(t₀)` inside the integral (legitimate as
`-φ' ≥ 0`), and the integration by parts is done on `G`.
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section7Z

/-- The zeros with `a < Im ≤ b`, `0 ≤ a`, are finitely many. -/
theorem finite_zeros_Ioc {a b : ℝ} (ha : 0 ≤ a) :
    (IEANTN.zetaZeroesIn Set.univ (Set.Ioc a b)).Finite := by
  set K : Set ℂ := {w | 0 ≤ w.re ∧ w.re ≤ 1 ∧ 0 ≤ w.im ∧ w.im ≤ |b|} with hK
  have hKc : IsCompact K := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    refine ⟨(isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const))), ?_⟩
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1 + |b|, fun w hw ↦ ?_⟩
    obtain ⟨h0, h1, h2, h3⟩ := hw
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 1 + |b| := by rw [abs_of_nonneg h0, abs_of_nonneg h2]; linarith
  have hmem : {w : ℂ | riemannZeta₁ w ≠ 0} ∈ codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ K)
      CH2ZetaInstance.riemannZeta₁_ne_zero_codiscrete
  refine (hKc.finite_sdiff_of_mem_codiscreteWithin hmem).subset ?_
  rintro w ⟨-, ⟨hw0, hw1⟩, hw⟩
  have hwpos : 0 < w.im := lt_of_le_of_lt ha hw0
  have hw1' : w ≠ 1 := by rintro rfl; simp at hwpos
  have hs := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hw hwpos.ne'
  refine ⟨⟨hs.1, hs.2, hwpos.le, hw1.trans (le_abs_self b)⟩, ?_⟩
  simp only [Set.mem_setOf_eq, not_not]
  rw [CH2ZetaInstance.riemannZeta₁_eq_mul hw1', hw, mul_zero]

/-- A zero sum over a finite zero set is a finite sum. -/
theorem zetaZeroesSum_eq_sum {J : Set ℝ} (hfin : (IEANTN.zetaZeroesIn Set.univ J).Finite)
    (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ J f
      = ∑ ρ ∈ hfin.toFinset, f ρ * (IEANTN.zetaOrder ρ : ℝ) := by
  unfold IEANTN.zetaZeroesSum
  rw [tsum_subtype (IEANTN.zetaZeroesIn Set.univ J) (fun ρ ↦ f ρ * (IEANTN.zetaOrder ρ : ℝ)),
    tsum_eq_sum (s := hfin.toFinset)]
  · exact Finset.sum_congr rfl fun ρ hρ ↦
      Set.indicator_of_mem ((Set.Finite.mem_toFinset hfin).mp hρ) _
  · intro ρ hρ
    exact Set.indicator_of_notMem (fun h ↦ hρ ((Set.Finite.mem_toFinset hfin).mpr h)) _

theorem zetaOrder_nonneg_of_mem {J : Set ℝ} (hJ : J ⊆ Set.Ioi 0) {ρ : ℂ}
    (hρ : ρ ∈ IEANTN.zetaZeroesIn Set.univ J) : (0 : ℝ) ≤ IEANTN.zetaOrder ρ := by
  have him : 0 < ρ.im := hJ hρ.2.1
  have h1 : ρ ≠ 1 := by rintro rfl; simp at him
  exact_mod_cast CH2Section6.zetaOrder_nonneg_of_ne_one h1

/-- `N(s)` as a sum over the zeros up to a larger height `t₁`. -/
theorem zetaNClosed_eq_sum {t₁ s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ t₁) :
    ZeroCount.v1.zetaNClosed s = ∑ ρ ∈ (finite_zeros_Ioc (a := 0) (b := t₁) le_rfl).toFinset,
      (if ρ.im ≤ s then (IEANTN.zetaOrder ρ : ℝ) else 0) := by
  set hfin := finite_zeros_Ioc (a := 0) (b := t₁) le_rfl
  rw [ZeroCount.v1.zetaNClosed, zetaZeroesSum_eq_sum (finite_zeros_Ioc (a := 0) (b := s) le_rfl)]
  have hsub : (finite_zeros_Ioc (a := 0) (b := s) le_rfl).toFinset ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨hρ.1, ⟨hρ.2.1.1, hρ.2.1.2.trans hs⟩, hρ.2.2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [Set.Finite.mem_toFinset] at hρ
    rw [if_pos hρ.2.1.2, one_mul]
  · intro ρ hρ hρ'
    rw [Set.Finite.mem_toFinset] at hρ hρ'
    rw [if_neg]
    intro hle
    exact hρ' ⟨hρ.1, ⟨hρ.2.1.1, hle⟩, hρ.2.2⟩

/-- **`lem:Lehmanmodern`, eq. `seguitor`.** -/
theorem lehman_antitone (hrvm : ZeroCount.v1.rvm_error_bound) {t₀ t₁ : ℝ} (h1 : 1 ≤ t₀)
    (h01 : t₀ ≤ t₁) {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc t₀ t₁)) (hneg : ∀ t ∈ Set.Icc t₀ t₁, φ' t ≤ 0)
    (hpos : 0 ≤ φ t₁) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      ≤ (∫ t in t₀..t₁, φ t * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t)))
        + φ t₀ * (Real.log t₀ / 5 + 2
          - (ZeroCount.v1.zetaNClosed t₀ - ZeroCount.v1.rvmMain t₀)) := by
  have hπ := Real.pi_pos
  have ht0 : 0 < t₀ := by linarith
  set hfin := finite_zeros_Ioc (a := 0) (b := t₁) le_rfl
  set S := hfin.toFinset with hS
  set m : ℂ → ℝ := fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ) with hm
  have hm0 : ∀ ρ ∈ S, 0 ≤ m ρ := fun ρ hρ ↦
    zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self ((Set.Finite.mem_toFinset hfin).mp hρ)
  set c : ℝ → ℝ := fun t ↦ ∑ ρ ∈ S, (if ρ.im ≤ t then m ρ else 0) with hc_def
  -- the sum as a sum over `S`
  have hsum : IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      = ∑ ρ ∈ S, (if t₀ < ρ.im then φ ρ.im * m ρ else 0) := by
    rw [zetaZeroesSum_eq_sum (finite_zeros_Ioc (a := t₀) (b := t₁) ht0.le)]
    have hsub : (finite_zeros_Ioc (a := t₀) (b := t₁) ht0.le).toFinset ⊆ S := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ ⊢
      exact ⟨hρ.1, ⟨ht0.trans hρ.2.1.1, hρ.2.1.2⟩, hρ.2.2⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
      rw [Set.Finite.mem_toFinset] at hρ
      rw [if_pos hρ.2.1.1]
    · intro ρ hρ hρ'
      rw [Set.Finite.mem_toFinset] at hρ hρ'
      rw [if_neg]
      intro hlt
      exact hρ' ⟨hρ.1, ⟨hlt, hρ.2.1.2⟩, hρ.2.2⟩
  -- per zero: `φ(γ) = φ(t₁) - ∫_{t₀}^{t₁} 1_{γ ≤ t} φ'(t) dt`
  have hφ'int : IntegrableOn φ' (Set.Icc t₀ t₁) := by
    rw [← Set.uIcc_of_le h01]; exact hc.integrableOn_compact isCompact_uIcc
  have hftc : ∀ γ : ℝ, t₀ < γ → γ ≤ t₁ →
      φ γ = φ t₁ - ∫ t in t₀..t₁, (Set.Ici γ).indicator φ' t := by
    intro γ hγ0 hγ1
    have hI : (∫ t in t₀..t₁, (Set.Ici γ).indicator φ' t) = ∫ t in γ..t₁, φ' t := by
      rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le hγ1,
        integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        show Set.Ici γ ∩ Set.Ioc t₀ t₁ = Set.Icc γ t₁ by
          ext t; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
          constructor
          · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩,
        integral_Icc_eq_integral_Ioc]
    rw [hI, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hd t (by
        rw [Set.uIcc_of_le hγ1] at ht; rw [Set.uIcc_of_le h01]; exact ⟨by linarith [ht.1], ht.2⟩))
      ((hc.mono (by rw [Set.uIcc_of_le hγ1, Set.uIcc_of_le h01]; exact Set.Icc_subset_Icc_left hγ0.le)).intervalIntegrable)]
    ring
  -- the swap
  have hind_int : ∀ γ : ℝ, IntervalIntegrable ((Set.Ici γ).indicator φ') volume t₀ t₁ := by
    intro γ
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h01]
    exact hφ'int.indicator measurableSet_Ici
  have hswap : ∑ ρ ∈ S, (if t₀ < ρ.im then m ρ * ∫ t in t₀..t₁, (Set.Ici ρ.im).indicator φ' t else 0)
      = ∫ t in t₀..t₁, φ' t * (c t - c t₀) := by
    have e1 : ∀ ρ ∈ S, (if t₀ < ρ.im then m ρ * ∫ t in t₀..t₁, (Set.Ici ρ.im).indicator φ' t else 0)
        = ∫ t in t₀..t₁, (if t₀ < ρ.im then m ρ * (Set.Ici ρ.im).indicator φ' t else 0) := by
      intro ρ _
      split_ifs
      · rw [intervalIntegral.integral_const_mul]
      · simp
    rw [Finset.sum_congr rfl e1, ← intervalIntegral.integral_finset_sum]
    · refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le h01] at ht
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      by_cases h0 : t₀ < ρ.im
      · rw [if_pos h0, if_neg (not_le.mpr h0), sub_zero]
        by_cases h2 : ρ.im ≤ t
        · rw [Set.indicator_of_mem (show t ∈ Set.Ici ρ.im from h2), if_pos h2]; ring
        · rw [Set.indicator_of_notMem (show t ∉ Set.Ici ρ.im from h2), if_neg h2]; ring
      · rw [if_neg h0, if_pos (not_lt.mp h0), if_pos ((not_lt.mp h0).trans ht.1)]; ring
    · intro ρ _
      split_ifs
      · exact (hind_int ρ.im).const_mul _
      · exact intervalIntegrable_const
  -- the count is bounded by the smooth `G`
  set B : ℝ → ℝ := fun t ↦ Real.log t / 5 + 2 with hB
  set G : ℝ → ℝ := fun t ↦ ZeroCount.v1.rvmMain t + B t - ZeroCount.v1.zetaNClosed t₀ with hG
  have hcN : ∀ t ∈ Set.Icc t₀ t₁, c t - c t₀ = ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀ := by
    intro t ht
    rw [zetaNClosed_eq_sum (by linarith [ht.1]) ht.2, zetaNClosed_eq_sum ht0.le h01]
  have hcG : ∀ t ∈ Set.Icc t₀ t₁, c t - c t₀ ≤ G t := by
    intro t ht
    rw [hcN t ht]
    have := hrvm t (by linarith [ht.1])
    have := (abs_le.mp this).2
    simp only [hG, hB]
    linarith
  -- assemble
  have hmain : IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      = φ t₁ * (c t₁ - c t₀) - ∫ t in t₀..t₁, φ' t * (c t - c t₀) := by
    rw [hsum, ← hswap]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
    by_cases h0 : t₀ < ρ.im
    · rw [if_pos h0, if_pos h0, if_neg (not_le.mpr h0), if_pos hρ'.2.1.2,
        hftc ρ.im h0 hρ'.2.1.2]
      ring
    · rw [if_neg h0, if_neg h0, if_pos (not_lt.mp h0), if_pos ((not_lt.mp h0).trans h01)]
      ring
  -- `-∫ φ' (c - c₀) ≤ -∫ φ' G`
  have hGd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt G
      (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t)) t := by
    intro t ht
    rw [Set.uIcc_of_le h01] at ht
    have htp : 0 < t := by linarith [ht.1]
    have hM : HasDerivAt ZeroCount.v1.rvmMain (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) t := by
      unfold ZeroCount.v1.rvmMain
      have h2 : HasDerivAt (fun t : ℝ ↦ t / (2 * Real.pi)) (1 / (2 * Real.pi)) t := by
        simpa using (hasDerivAt_id t).div_const (2 * Real.pi)
      have hlog := (Real.hasDerivAt_log (by positivity : t / (2 * Real.pi) ≠ 0)).comp t h2
      refine (((h2.mul hlog).sub h2).add_const (7 / 8 : ℝ)).congr_deriv ?_
      have : t / (2 * Real.pi) ≠ 0 := by positivity
      simp only [Function.comp_apply]
      field_simp
      ring
    have hBd : HasDerivAt B (1 / (5 * t)) t := by
      refine (((Real.hasDerivAt_log htp.ne').div_const 5).add_const (2 : ℝ)).congr_deriv ?_
      field_simp
    exact (hM.add hBd).sub_const (ZeroCount.v1.zetaNClosed t₀)
  have hGc : ContinuousOn (fun t ↦ Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t))
      (Set.uIcc t₀ t₁) := by
    intro t ht
    rw [Set.uIcc_of_le h01] at ht
    have htp : 0 < t := by linarith [ht.1]
    refine ContinuousAt.continuousWithinAt ?_
    have : t / (2 * Real.pi) ≠ 0 := by positivity
    fun_prop (disch := first | assumption | positivity)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hGd hd hGc.intervalIntegrable
    hc.intervalIntegrable
  have hle : -∫ t in t₀..t₁, φ' t * (c t - c t₀) ≤ -∫ t in t₀..t₁, G t * φ' t := by
    rw [neg_le_neg_iff]
    refine intervalIntegral.integral_mono_on h01 ?_ ?_ fun t ht ↦ ?_
    · exact (ContinuousOn.mul (fun t ht ↦ (hGd t ht).continuousAt.continuousWithinAt) hc).intervalIntegrable
    · -- integrability of `φ'(c - c₀)`
      have hsI : IntervalIntegrable (∑ ρ ∈ S, fun t ↦ (if t₀ < ρ.im then m ρ * (Set.Ici ρ.im).indicator φ' t else 0)) volume t₀ t₁ := by
        refine IntervalIntegrable.sum S fun ρ _ ↦ ?_
        split_ifs
        · exact (hind_int ρ.im).const_mul _
        · exact intervalIntegrable_const
      refine hsI.congr fun t ht ↦ ?_
      rw [Set.uIoc_of_le h01] at ht
      simp only [Finset.sum_apply]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ ↦ ?_
      by_cases h0 : t₀ < ρ.im
      · rw [if_pos h0, if_neg (not_le.mpr h0), sub_zero]
        by_cases h2 : ρ.im ≤ t
        · rw [Set.indicator_of_mem (show t ∈ Set.Ici ρ.im from h2), if_pos h2]; ring
        · rw [Set.indicator_of_notMem (show t ∉ Set.Ici ρ.im from h2), if_neg h2]; ring
      · rw [if_neg h0, if_pos (not_lt.mp h0), if_pos ((not_lt.mp h0).trans ht.1.le)]; ring
    · have h1' := hcG t ht
      have h2' := hneg t ht
      nlinarith
  rw [hmain]
  have hend := mul_le_mul_of_nonneg_left (hcG t₁ ⟨h01, le_rfl⟩) hpos
  have e : (∫ t in t₀..t₁, φ t * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t)))
      = ∫ t in t₀..t₁, (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t)) * φ t := by
    congr 1; funext t; ring
  rw [e]
  simp only [hG, hB] at hibp hend ⊢
  linarith

end CH2Section7Z
