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

/-! ### `cor:brut` and `lem:cathinv` -/

/-- `log t ≤ t/e`. -/
theorem log_le_div_exp_one {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / Real.exp 1 := by
  have h := Real.add_one_le_exp (t / Real.exp 1 - 1)
  have he : Real.exp (t / Real.exp 1 - 1) = Real.exp (t / Real.exp 1) / Real.exp 1 := by
    rw [Real.exp_sub]
  have hlog : Real.log t - 1 ≤ t / Real.exp 1 - 1 := by
    have h2 : Real.log (t / Real.exp 1) ≤ t / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h2
    exact h2
  linarith

/-- `Q(t) ≤ log t/5 + 2` in the form `N ≤ M + log t/5 + 2`, and `N ≤ M + 1` below `280`. -/
theorem zetaN_le (hrvm : ZeroCount.v1.rvm_error_bound) {t : ℝ} (ht : 1 ≤ t) :
    ZeroCount.v1.zetaNClosed t ≤ ZeroCount.v1.rvmMain t + Real.log t / 5 + 2 := by
  have := (abs_le.mp (hrvm t ht)).2
  linarith

/-- **`cor:brut`**, from `T ≥ 12`: `N(T) ≤ (T/2π) log(T/2π)`. -/
theorem zetaN_le_brut (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small) {T : ℝ} (hT : 12 ≤ T) :
    ZeroCount.v1.zetaNClosed T ≤ T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) := by
  have hπ := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  suffices h : ZeroCount.v1.zetaNClosed T - ZeroCount.v1.rvmMain T + 7 / 8 ≤ T / (2 * Real.pi) by
    unfold ZeroCount.v1.rvmMain at h; linarith
  rcases le_or_gt T 280 with h280 | h280
  · have := (abs_lt.mp (hsmall T (by linarith) h280)).2
    have : (15 / 8 : ℝ) ≤ T / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  · have h1 := zetaN_le hrvm (by linarith : (1:ℝ) ≤ T)
    have h2 := log_le_div_exp_one (by linarith : (0:ℝ) < T)
    have he := Real.exp_one_gt_d9
    have h3 : T / Real.exp 1 ≤ T / 2.7182818283 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) he.le
    have h4 : T / 2.7182818283 / 5 + 2 + 7 / 8 ≤ T / (2 * Real.pi) := by
      rw [div_div, le_div_iff₀ (by positivity)]
      have : (T / (2.7182818283 * 5) + 2 + 7 / 8) * (2 * Real.pi)
          ≤ (T / (2.7182818283 * 5) + 2 + 7 / 8) * 6.3 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have e : (T / (2.7182818283 * 5) + 2 + 7 / 8) * 6.3 = T * (6.3 / (2.7182818283 * 5)) + 18.1125 := by
        ring
      have : 6.3 / (2.7182818283 * 5) ≤ (0.47 : ℝ) := by norm_num
      nlinarith
    linarith

/-- **`lem:cathinv`**, up to a finite height: for `14 ≤ t₀ ≤ t₁`,
`∑_{t₀ < γ ≤ t₁} 1/γ² ≤ log(e t₀/2π)/(2π t₀) + (2 log t₀/5 + 41/10)/t₀²`. -/
theorem sum_inv_sq_le (hrvm : ZeroCount.v1.rvm_error_bound) {t₀ t₁ : ℝ} (h14 : 14 ≤ t₀)
    (h01 : t₀ ≤ t₁) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ 1 / ρ.im ^ 2)
      ≤ Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
        + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_d2
  have ht0 : 0 < t₀ := by linarith
  have hpos : ∀ t ∈ Set.uIcc t₀ t₁, 0 < t := by
    intro t ht; rw [Set.uIcc_of_le h01] at ht; linarith [ht.1]
  have hL := lehman_antitone hrvm (φ := fun t ↦ 1 / t ^ 2) (φ' := fun t ↦ -2 / t ^ 3)
    (by linarith) h01
    (fun t ht ↦ by
      have htp := hpos t ht
      have := ((hasDerivAt_pow 2 t).inv (by positivity))
      simp only [one_div]
      refine this.congr_deriv ?_
      field_simp; ring)
    (fun t ht ↦ ((continuousAt_const.div (continuousAt_id.pow 3)
      (pow_ne_zero 3 (hpos t ht).ne')).continuousWithinAt))
    (fun t ht ↦ by
      have : 0 < t := by linarith [ht.1]
      have : 0 < t ^ 3 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le)
    (by have : 0 < t₁ := by linarith
        positivity)
  -- the integral, exactly
  set A : ℝ → ℝ := fun t ↦ -(Real.log (Real.exp 1 * t / (2 * Real.pi)) / (2 * Real.pi * t))
    - 1 / (10 * t ^ 2) with hA
  have hAd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt A
      (1 / t ^ 2 * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t))) t := by
    intro t ht
    have htp := hpos t ht
    have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (Real.exp 1 * t / (2 * Real.pi))) (1 / t) t := by
      have h1 : HasDerivAt (fun t : ℝ ↦ Real.exp 1 * t / (2 * Real.pi))
          (Real.exp 1 / (2 * Real.pi)) t := by
        simpa using ((hasDerivAt_id t).const_mul (Real.exp 1)).div_const (2 * Real.pi)
      refine ((Real.hasDerivAt_log (by positivity)).comp t h1).congr_deriv ?_
      field_simp
    have h2 : HasDerivAt (fun t : ℝ ↦ 2 * Real.pi * t) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    have h3 : HasDerivAt (fun t : ℝ ↦ 10 * t ^ 2) (10 * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul 10
    have := ((hlog.div h2 (by positivity)).neg).sub ((hasDerivAt_const t (1:ℝ)).div h3 (by positivity))
    refine this.congr_deriv ?_
    have hl : Real.log (Real.exp 1 * t / (2 * Real.pi)) = 1 + Real.log (t / (2 * Real.pi)) := by
      rw [mul_div_assoc, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    rw [hl]
    field_simp
    ring
  have hint : (∫ t in t₀..t₁, 1 / t ^ 2 * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t)))
      = A t₁ - A t₀ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt hAd ?_
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    have htp := hpos t ht
    have : t / (2 * Real.pi) ≠ 0 := by positivity
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop (disch := first | assumption | positivity)
  have ht1 : 0 < t₁ := by linarith
  have hAt1 : A t₁ ≤ 0 := by
    simp only [hA]
    have : 0 ≤ Real.log (Real.exp 1 * t₁ / (2 * Real.pi)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.exp_one_gt_d9]
    have : 0 ≤ Real.log (Real.exp 1 * t₁ / (2 * Real.pi)) / (2 * Real.pi * t₁) := by positivity
    have : 0 ≤ 1 / (10 * t₁ ^ 2) := by positivity
    linarith
  have hQ := (abs_le.mp (hrvm t₀ (by linarith))).1
  rw [hint] at hL
  have hphi : 0 ≤ 1 / t₀ ^ 2 := by positivity
  have hQ' : 1 / t₀ ^ 2 * (Real.log t₀ / 5 + 2
      - (ZeroCount.v1.zetaNClosed t₀ - ZeroCount.v1.rvmMain t₀))
      ≤ 1 / t₀ ^ 2 * (2 * Real.log t₀ / 5 + 4) := by
    apply mul_le_mul_of_nonneg_left _ hphi; linarith
  have hfin : -A t₀ + 1 / t₀ ^ 2 * (2 * Real.log t₀ / 5 + 4)
      = Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
        + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2 := by
    simp only [hA]; field_simp; ring
  linarith

end CH2Section7Z
