/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section7Vihuela

/-!
# Section 8.1: `lem:janframe`

`∑_{|γ - t| > a} 1/|t - γ|² ≤ (1/πa) log(t/2π) + (2 log t/5 + 4 + Q(t - a) - Q(t + a))/a² + ε`,
the sum over all non-trivial zeros, via `lem:Lehmanmodern` in both monotone directions and
`lem:daremo`. Zero counts use half-open intervals `(u, v]` throughout, so the paper's `Q((t-a)⁻)` is
`Q(t - a)` here and the zeros at `t - a` belong to the outer sum.
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section81

theorem lehman_identity {t₀ t₁ : ℝ} (ht0 : 0 < t₀)
    (h01 : t₀ ≤ t₁) {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc t₀ t₁)) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
        = φ t₁ * (ZeroCount.v1.zetaNClosed t₁ - ZeroCount.v1.zetaNClosed t₀)
          - ∫ t in t₀..t₁, φ' t * (ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀) ∧
      IntervalIntegrable (fun t ↦ φ' t * (ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀))
        MeasureTheory.volume t₀ t₁ := by
  set hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t₁) le_rfl
  set S := hfin.toFinset with hS
  set m : ℂ → ℝ := fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ) with hm
  have hm0 : ∀ ρ ∈ S, 0 ≤ m ρ := fun ρ hρ ↦
    CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self ((Set.Finite.mem_toFinset hfin).mp hρ)
  set c : ℝ → ℝ := fun t ↦ ∑ ρ ∈ S, (if ρ.im ≤ t then m ρ else 0) with hc_def
  -- the sum as a sum over `S`
  have hsum : IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      = ∑ ρ ∈ S, (if t₀ < ρ.im then φ ρ.im * m ρ else 0) := by
    rw [CH2Section7Z.zetaZeroesSum_eq_sum (CH2Section7Z.finite_zeros_Ioc (a := t₀) (b := t₁) ht0.le)]
    have hsub : (CH2Section7Z.finite_zeros_Ioc (a := t₀) (b := t₁) ht0.le).toFinset ⊆ S := by
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
  have hcN : ∀ t ∈ Set.Icc t₀ t₁, c t - c t₀ = ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀ := by
    intro t ht
    rw [CH2Section7Z.zetaNClosed_eq_sum (by linarith [ht.1]) ht.2,
      CH2Section7Z.zetaNClosed_eq_sum ht0.le h01]
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
  have hint : IntervalIntegrable (fun t ↦ φ' t * (c t - c t₀)) MeasureTheory.volume t₀ t₁ := by
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
  have hcong : ∀ t ∈ Set.uIoc t₀ t₁, φ' t * (c t - c t₀)
      = φ' t * (ZeroCount.v1.zetaNClosed t - ZeroCount.v1.zetaNClosed t₀) := by
    intro t ht
    rw [Set.uIoc_of_le h01] at ht
    rw [hcN t ⟨ht.1.le, ht.2⟩]
  refine ⟨?_, hint.congr hcong⟩
  rw [hmain, hcN t₁ ⟨h01, le_rfl⟩, intervalIntegral.integral_congr_ae
    (Filter.Eventually.of_forall fun t ht ↦ hcong t ht)]

theorem hasDerivAt_rvmMain {t : ℝ} (ht : 0 < t) :
    HasDerivAt ZeroCount.v1.rvmMain (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) t := by
  have hπ := Real.pi_pos
  unfold ZeroCount.v1.rvmMain
  have h2 : HasDerivAt (fun t : ℝ ↦ t / (2 * Real.pi)) (1 / (2 * Real.pi)) t := by
    simpa using (hasDerivAt_id t).div_const (2 * Real.pi)
  have hlog := (Real.hasDerivAt_log (by positivity : t / (2 * Real.pi) ≠ 0)).comp t h2
  refine (((h2.mul hlog).sub h2).add_const (7 / 8 : ℝ)).congr_deriv ?_
  have : t / (2 * Real.pi) ≠ 0 := by positivity
  simp only [Function.comp_apply]
  field_simp
  ring

theorem hasDerivAt_Bq {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ ↦ Real.log t / 5 + 2) (1 / (5 * t)) t := by
  refine (((Real.hasDerivAt_log ht.ne').div_const 5).add_const (2 : ℝ)).congr_deriv ?_
  field_simp

theorem continuousOn_lehman_weight {t₀ t₁ : ℝ} (ht0 : 0 < t₀) (h01 : t₀ ≤ t₁) (c : ℝ) :
    ContinuousOn (fun t ↦ Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + c * (1 / (5 * t)))
      (Set.uIcc t₀ t₁) := by
  intro t ht
  rw [Set.uIcc_of_le h01] at ht
  have htp : 0 < t := by linarith [ht.1]
  have hπ := Real.pi_pos
  refine ContinuousAt.continuousWithinAt ?_
  have : t / (2 * Real.pi) ≠ 0 := by positivity
  have : 5 * t ≠ 0 := by positivity
  fun_prop (disch := first | assumption | positivity)

/-- **`lem:Lehmanmodern`, decreasing `φ`**, with the endpoint remainder `Q(t₁)` kept. -/
theorem lehman_dec (hrvm : ZeroCount.v1.rvm_error_bound) {t₀ t₁ : ℝ} (h1 : 1 ≤ t₀)
    (h01 : t₀ ≤ t₁) {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc t₀ t₁)) (hneg : ∀ t ∈ Set.Icc t₀ t₁, φ' t ≤ 0) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      ≤ (∫ t in t₀..t₁, φ t * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * t))))
        + φ t₁ * ((ZeroCount.v1.zetaNClosed t₁ - ZeroCount.v1.rvmMain t₁) - (Real.log t₁ / 5 + 2))
        + φ t₀ * ((Real.log t₀ / 5 + 2) - (ZeroCount.v1.zetaNClosed t₀ - ZeroCount.v1.rvmMain t₀)) := by
  have ht0 : 0 < t₀ := by linarith
  obtain ⟨hid, hint⟩ := lehman_identity ht0 h01 hd hc
  set N := ZeroCount.v1.zetaNClosed
  set M := ZeroCount.v1.rvmMain
  set G : ℝ → ℝ := fun t ↦ M t + (Real.log t / 5 + 2) - N t₀ with hG
  have hGd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt G
      (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * t))) t := by
    intro t ht
    rw [Set.uIcc_of_le h01] at ht
    have htp : 0 < t := by linarith [ht.1]
    exact (((hasDerivAt_rvmMain htp).add (hasDerivAt_Bq htp)).sub_const (N t₀)).congr_deriv
      (by ring)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hGd hd
    (continuousOn_lehman_weight ht0 h01 1).intervalIntegrable hc.intervalIntegrable
  have hle : -∫ t in t₀..t₁, φ' t * (N t - N t₀) ≤ -∫ t in t₀..t₁, G t * φ' t := by
    rw [neg_le_neg_iff]
    refine intervalIntegral.integral_mono_on h01
      (ContinuousOn.mul (fun t ht ↦ (hGd t ht).continuousAt.continuousWithinAt) hc).intervalIntegrable
      hint fun t ht ↦ ?_
    have hb := (abs_le.mp (hrvm t (by linarith [ht.1]))).2
    have h2' := hneg t ht
    simp only [hG]
    nlinarith
  rw [hid]
  have e : (∫ t in t₀..t₁, φ t * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * t))))
      = ∫ t in t₀..t₁, (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * t))) * φ t := by
    congr 1; funext t; ring
  rw [e]
  simp only [hG] at hibp
  linarith

/-- **`lem:Lehmanmodern`, increasing `φ`** (eq. `sagasto`). -/
theorem lehman_inc (hrvm : ZeroCount.v1.rvm_error_bound) {t₀ t₁ : ℝ} (h1 : 1 ≤ t₀)
    (h01 : t₀ ≤ t₁) {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc t₀ t₁)) (hpos : ∀ t ∈ Set.Icc t₀ t₁, 0 ≤ φ' t) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ φ ρ.im)
      ≤ (∫ t in t₀..t₁, φ t * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + (-1) * (1 / (5 * t))))
        + φ t₁ * ((ZeroCount.v1.zetaNClosed t₁ - ZeroCount.v1.rvmMain t₁) + (Real.log t₁ / 5 + 2))
        - φ t₀ * ((ZeroCount.v1.zetaNClosed t₀ - ZeroCount.v1.rvmMain t₀) + (Real.log t₀ / 5 + 2)) := by
  have ht0 : 0 < t₀ := by linarith
  obtain ⟨hid, hint⟩ := lehman_identity ht0 h01 hd hc
  set N := ZeroCount.v1.zetaNClosed
  set M := ZeroCount.v1.rvmMain
  set G : ℝ → ℝ := fun t ↦ M t - (Real.log t / 5 + 2) - N t₀ with hG
  have hGd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt G
      (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + (-1) * (1 / (5 * t))) t := by
    intro t ht
    rw [Set.uIcc_of_le h01] at ht
    have htp : 0 < t := by linarith [ht.1]
    exact (((hasDerivAt_rvmMain htp).sub (hasDerivAt_Bq htp)).sub_const (N t₀)).congr_deriv
      (by ring)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hGd hd
    (continuousOn_lehman_weight ht0 h01 (-1)).intervalIntegrable hc.intervalIntegrable
  have hle : -∫ t in t₀..t₁, φ' t * (N t - N t₀) ≤ -∫ t in t₀..t₁, G t * φ' t := by
    rw [neg_le_neg_iff]
    refine intervalIntegral.integral_mono_on h01
      (ContinuousOn.mul (fun t ht ↦ (hGd t ht).continuousAt.continuousWithinAt) hc).intervalIntegrable
      hint fun t ht ↦ ?_
    have hb := (abs_le.mp (hrvm t (by linarith [ht.1]))).1
    have h2' := hpos t ht
    simp only [hG]
    nlinarith
  rw [hid]
  have e : (∫ t in t₀..t₁, φ t * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + (-1) * (1 / (5 * t))))
      = ∫ t in t₀..t₁, (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + (-1) * (1 / (5 * t))) * φ t := by
    congr 1; funext t; ring
  rw [e]
  simp only [hG] at hibp
  linarith

end CH2Section81
