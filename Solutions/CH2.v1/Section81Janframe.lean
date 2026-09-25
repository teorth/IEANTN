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

/-! ### The three integrals of `lem:janframe` (`lem:daremo`), with explicit antiderivatives -/

/-- Right of `t`: `∫_{t+a}^Y (log(y/2π)/(2π) + 1/(5y))/(y-t)² ≤ log((t+a)/2π)/(2πa) + log(1+t/a)/(2πt) + 1/(5ta)`. -/
theorem integral_right_le {t a Y : ℝ} (ht : 2 * Real.pi ≤ t) (ha : 0 < a) (hY : t + a ≤ Y) :
    (∫ y in (t + a)..Y, (1 / (y - t) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * y))))
      ≤ Real.log ((t + a) / (2 * Real.pi)) / (2 * Real.pi * a)
        + Real.log (1 + t / a) / (2 * Real.pi * t) + 1 / (5 * t * a) := by
  have hπ := Real.pi_pos
  have ht0 : 0 < t := by linarith
  set G : ℝ → ℝ := fun y ↦ (1 / (2 * Real.pi)) * (-(Real.log (y / (2 * Real.pi)) / (y - t))
      + (1 / t) * Real.log ((y - t) / y)) + (1 / 5) * ((1 / t ^ 2) * Real.log (y / (y - t)) - 1 / (t * (y - t)))
    with hG
  have hmem : ∀ y ∈ Set.uIcc (t + a) Y, 0 < y - t ∧ 0 < y := by
    intro y hy; rw [Set.uIcc_of_le hY] at hy; constructor <;> linarith [hy.1]
  have hd : ∀ y ∈ Set.uIcc (t + a) Y, HasDerivAt G
      ((1 / (y - t) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * y)))) y := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    have hyt : HasDerivAt (fun y : ℝ ↦ y - t) 1 y := by simpa using (hasDerivAt_id y).sub_const t
    have hy2 : HasDerivAt (fun y : ℝ ↦ y / (2 * Real.pi)) (1 / (2 * Real.pi)) y := by
      simpa using (hasDerivAt_id y).div_const (2 * Real.pi)
    have hlog1 := hy2.log (by positivity : y / (2 * Real.pi) ≠ 0)
    have hq1 : HasDerivAt (fun y : ℝ ↦ (y - t) / y) (t / y ^ 2) y := by
      refine (hyt.div (hasDerivAt_id y) h2.ne').congr_deriv ?_
      simp only [id]; field_simp; ring
    have hlog2 := hq1.log (by positivity : (y - t) / y ≠ 0)
    have hq2 : HasDerivAt (fun y : ℝ ↦ y / (y - t)) (-t / (y - t) ^ 2) y := by
      refine ((hasDerivAt_id y).div hyt h1.ne').congr_deriv ?_
      simp only [id]; field_simp; ring
    have hlog3 := hq2.log (by positivity : y / (y - t) ≠ 0)
    have hinv : HasDerivAt (fun y : ℝ ↦ 1 / (t * (y - t))) (-(t) / (t * (y - t)) ^ 2) y := by
      have := ((hyt.const_mul t).inv (by positivity))
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by simp [one_div])).congr_deriv ?_
      ring
    have H := ((((hlog1.div hyt h1.ne').neg).add (hlog2.const_mul (1 / t))).const_mul (1 / (2 * Real.pi))).add
      (((hlog3.const_mul (1 / t ^ 2)).sub hinv).const_mul (1 / 5))
    refine H.congr_deriv ?_
    try simp only [Function.comp_apply]
    field_simp
    ring
  have hcont : ContinuousOn (fun y ↦ (1 / (y - t) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi)
      + 1 * (1 / (5 * y)))) (Set.uIcc (t + a) Y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    have : (y - t) ^ 2 ≠ 0 := by positivity
    have : y / (2 * Real.pi) ≠ 0 := by positivity
    have : 5 * y ≠ 0 := by positivity
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  -- `G Y ≤ 0`
  have hYt : 0 < Y - t := by linarith
  have hYp : 0 < Y := by linarith
  have hGY : G Y ≤ 0 := by
    simp only [hG]
    have h1 : 0 ≤ Real.log (Y / (2 * Real.pi)) / (Y - t) := by
      apply div_nonneg _ hYt.le; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : Real.log ((Y - t) / Y) ≤ 0 := Real.log_nonpos (by positivity) (by rw [div_le_one hYp]; linarith)
    have h3 : (1 / t ^ 2) * Real.log (Y / (Y - t)) ≤ 1 / (t * (Y - t)) := by
      have hl := Real.log_le_sub_one_of_pos (show 0 < Y / (Y - t) by positivity)
      have e : Y / (Y - t) - 1 = t / (Y - t) := by field_simp; ring
      rw [e] at hl
      calc (1 / t ^ 2) * Real.log (Y / (Y - t)) ≤ (1 / t ^ 2) * (t / (Y - t)) :=
            mul_le_mul_of_nonneg_left hl (by positivity)
        _ = 1 / (t * (Y - t)) := by field_simp
    have : (1 / t) * Real.log ((Y - t) / Y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
    have : 0 < 1 / (2 * Real.pi) := by positivity
    nlinarith
  -- `-G(t+a)`
  have e1 : t + a - t = a := by ring
  have hGa : -G (t + a) = Real.log ((t + a) / (2 * Real.pi)) / (2 * Real.pi * a)
      + Real.log (1 + t / a) / (2 * Real.pi * t)
      + (1 / (5 * t * a) - (1 / 5) * (1 / t ^ 2) * Real.log ((t + a) / a)) := by
    simp only [hG, e1]
    rw [show (a / (t + a)) = ((t + a) / a)⁻¹ by field_simp, Real.log_inv,
      show (1 + t / a) = (t + a) / a by field_simp; ring]
    field_simp
    ring
  have hlog_pos : 0 ≤ (1 / 5) * (1 / t ^ 2) * Real.log ((t + a) / a) := by
    have : 0 ≤ Real.log ((t + a) / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
    positivity
  linarith

/-- Left of `t`: `∫_{y₀}^{t-a} (log(y/2π)/(2π))/(t-y)² ≤ log((t-a)/2π)/(2πa)` for `2π ≤ y₀`, `2y₀ ≤ t`. -/
theorem integral_left_le {t a y₀ : ℝ} (hy0 : 2 * Real.pi ≤ y₀) (hty : 2 * y₀ ≤ t) (ha : 0 < a)
    (ha1 : a ≤ 1) (hya : y₀ ≤ t - a) :
    (∫ y in y₀..(t - a), (1 / (t - y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi) + (-1) * (1 / (5 * y))))
      ≤ Real.log ((t - a) / (2 * Real.pi)) / (2 * Real.pi * a) := by
  have hπ := Real.pi_pos
  have hy00 : 0 < y₀ := by linarith
  have hmem : ∀ y ∈ Set.uIcc y₀ (t - a), 0 < t - y ∧ 0 < y := by
    intro y hy; rw [Set.uIcc_of_le hya] at hy; constructor <;> linarith [hy.1, hy.2]
  set G : ℝ → ℝ := fun y ↦ (1 / (2 * Real.pi)) * (Real.log (y / (2 * Real.pi)) / (t - y)
      - (1 / t) * Real.log (y / (t - y))) with hG
  have hd : ∀ y ∈ Set.uIcc y₀ (t - a), HasDerivAt G
      ((1 / (t - y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi))) y := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    have hty' : HasDerivAt (fun y : ℝ ↦ t - y) (-1) y := by simpa using (hasDerivAt_id y).const_sub t
    have hy2 : HasDerivAt (fun y : ℝ ↦ y / (2 * Real.pi)) (1 / (2 * Real.pi)) y := by
      simpa using (hasDerivAt_id y).div_const (2 * Real.pi)
    have hlog1 := hy2.log (by positivity : y / (2 * Real.pi) ≠ 0)
    have hq : HasDerivAt (fun y : ℝ ↦ y / (t - y)) (t / (t - y) ^ 2) y := by
      refine ((hasDerivAt_id y).div hty' h1.ne').congr_deriv ?_
      simp only [id]; field_simp; ring
    have hlog2 := hq.log (by positivity : y / (t - y) ≠ 0)
    have H := ((hlog1.div hty' h1.ne').sub (hlog2.const_mul (1 / t))).const_mul (1 / (2 * Real.pi))
    refine H.congr_deriv ?_
    have : t ≠ 0 := by linarith
    try simp only [Function.comp_apply]
    field_simp
    ring
  have hcont : ContinuousOn (fun y ↦ (1 / (t - y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi)))
      (Set.uIcc y₀ (t - a)) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    have : (t - y) ^ 2 ≠ 0 := by positivity
    have : y / (2 * Real.pi) ≠ 0 := by positivity
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hmono : (∫ y in y₀..(t - a), (1 / (t - y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi)
      + (-1) * (1 / (5 * y)))) ≤ ∫ y in y₀..(t - a), (1 / (t - y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi)) := by
    refine intervalIntegral.integral_mono_on hya ?_ hcont.intervalIntegrable fun y hy ↦ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      intro y hy
      obtain ⟨h1, h2⟩ := hmem y hy
      have : (t - y) ^ 2 ≠ 0 := by positivity
      have : y / (2 * Real.pi) ≠ 0 := by positivity
      have : 5 * y ≠ 0 := by positivity
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
    · obtain ⟨h1, h2⟩ := hmem y (by rw [Set.uIcc_of_le hya]; exact hy)
      have : 0 ≤ (1 / (t - y) ^ 2) * (1 / (5 * y)) := by positivity
      nlinarith
  refine hmono.trans ?_
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  have ht0 : 0 < t := by linarith
  have e1 : t - (t - a) = a := by ring
  simp only [hG, e1]
  -- drop the non-positive pieces
  have h1 : 0 ≤ Real.log ((t - a) / a) := Real.log_nonneg (by
    rw [le_div_iff₀ ha]; linarith [Real.pi_gt_three])
  have h2 : Real.log (y₀ / (t - y₀)) ≤ 0 := Real.log_nonpos (by
    have : 0 < t - y₀ := by linarith
    positivity) (by rw [div_le_one (by linarith)]; linarith)
  have h3 : 0 ≤ Real.log (y₀ / (2 * Real.pi)) / (t - y₀) := by
    apply div_nonneg _ (by linarith); apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have e : (1 / (2 * Real.pi)) * (Real.log ((t - a) / (2 * Real.pi)) / a - (1 / t) * Real.log ((t - a) / a))
      - (1 / (2 * Real.pi)) * (Real.log (y₀ / (2 * Real.pi)) / (t - y₀) - (1 / t) * Real.log (y₀ / (t - y₀)))
      = Real.log ((t - a) / (2 * Real.pi)) / (2 * Real.pi * a)
        - (1 / (2 * Real.pi)) * ((1 / t) * Real.log ((t - a) / a)
          + Real.log (y₀ / (2 * Real.pi)) / (t - y₀) - (1 / t) * Real.log (y₀ / (t - y₀))) := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ (1 / (2 * Real.pi)) * ((1 / t) * Real.log ((t - a) / a)
      + Real.log (y₀ / (2 * Real.pi)) / (t - y₀) - (1 / t) * Real.log (y₀ / (t - y₀))) := by
    have : 0 ≤ (1 / t) * Real.log ((t - a) / a) := by positivity
    have : (1 / t) * Real.log (y₀ / (t - y₀)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
    have : 0 ≤ (1 / t) * Real.log ((t - a) / a) + Real.log (y₀ / (2 * Real.pi)) / (t - y₀)
        - (1 / t) * Real.log (y₀ / (t - y₀)) := by linarith
    positivity
  linarith

/-- The mirror side: `∫_{y₀}^Y (log(y/2π)/(2π) + 1/(5y))/(t+y)² ≤ log(y₀/2π)/(2π(t+y₀)) + log((t+y₀)/y₀)/(2πt) + 1/(5y₀(t+y₀))`. -/
theorem integral_mirror_le {t y₀ Y : ℝ} (hy0 : 2 * Real.pi ≤ y₀) (ht : 0 < t) (hY : y₀ ≤ Y) :
    (∫ y in y₀..Y, (1 / (t + y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * y))))
      ≤ Real.log (y₀ / (2 * Real.pi)) / (2 * Real.pi * (t + y₀))
        + Real.log ((t + y₀) / y₀) / (2 * Real.pi * t) + 1 / (5 * y₀ * (t + y₀)) := by
  have hπ := Real.pi_pos
  have hy00 : 0 < y₀ := by linarith
  have hmem : ∀ y ∈ Set.uIcc y₀ Y, 0 < t + y ∧ y₀ ≤ y := by
    intro y hy; rw [Set.uIcc_of_le hY] at hy; constructor <;> linarith [hy.1]
  set G : ℝ → ℝ := fun y ↦ (1 / (2 * Real.pi)) * (-(Real.log (y / (2 * Real.pi)) / (t + y))
      + (1 / t) * Real.log (y / (t + y))) with hG
  have hd : ∀ y ∈ Set.uIcc y₀ Y, HasDerivAt G
      ((1 / (t + y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi))) y := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    have hyp : 0 < y := by linarith
    have hty' : HasDerivAt (fun y : ℝ ↦ t + y) 1 y := by simpa using (hasDerivAt_id y).const_add t
    have hy2 : HasDerivAt (fun y : ℝ ↦ y / (2 * Real.pi)) (1 / (2 * Real.pi)) y := by
      simpa using (hasDerivAt_id y).div_const (2 * Real.pi)
    have hlog1 := hy2.log (by positivity : y / (2 * Real.pi) ≠ 0)
    have hq : HasDerivAt (fun y : ℝ ↦ y / (t + y)) (t / (t + y) ^ 2) y := by
      refine ((hasDerivAt_id y).div hty' h1.ne').congr_deriv ?_
      simp only [id]; field_simp; ring
    have hlog2 := hq.log (by positivity : y / (t + y) ≠ 0)
    have H := (((hlog1.div hty' h1.ne').neg).add (hlog2.const_mul (1 / t))).const_mul (1 / (2 * Real.pi))
    refine H.congr_deriv ?_
    try simp only [Function.comp_apply]
    field_simp
    ring
  have hcont : ContinuousOn (fun y ↦ (1 / (t + y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi)))
      (Set.uIcc y₀ Y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    have : (t + y) ^ 2 ≠ 0 := by positivity
    have : y / (2 * Real.pi) ≠ 0 := by have : 0 < y := by linarith
                                       positivity
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  -- split off the `1/(5y)` part and bound it by `1/(5 y₀) ∫ 1/(t+y)²`
  have hcont2 : ContinuousOn (fun y ↦ (1 / (t + y) ^ 2) * (1 / (5 * y₀))) (Set.uIcc y₀ Y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    have : (t + y) ^ 2 ≠ 0 := by positivity
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hmono : (∫ y in y₀..Y, (1 / (t + y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi) + 1 * (1 / (5 * y))))
      ≤ ∫ y in y₀..Y, ((1 / (t + y) ^ 2) * (Real.log (y / (2 * Real.pi)) / (2 * Real.pi))
          + (1 / (t + y) ^ 2) * (1 / (5 * y₀))) := by
    refine intervalIntegral.integral_mono_on hY ?_ (hcont.intervalIntegrable.add hcont2.intervalIntegrable)
      fun y hy ↦ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      intro y hy
      obtain ⟨h1, h2⟩ := hmem y hy
      have hyp : 0 < y := by linarith
      have : (t + y) ^ 2 ≠ 0 := by positivity
      have : y / (2 * Real.pi) ≠ 0 := by positivity
      have : 5 * y ≠ 0 := by positivity
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
    · have hy0y := hy.1
      have hyp : 0 < y := by linarith
      have h5 : 1 / (5 * y) ≤ 1 / (5 * y₀) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      have : 0 ≤ 1 / (t + y) ^ 2 := by positivity
      nlinarith
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add hcont.intervalIntegrable hcont2.intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  -- `∫ 1/(t+y)² ≤ 1/(t+y₀)`
  have hd2 : ∀ y ∈ Set.uIcc y₀ Y, HasDerivAt (fun y ↦ -(1 / (t + y)) * (1 / (5 * y₀)))
      ((1 / (t + y) ^ 2) * (1 / (5 * y₀))) y := by
    intro y hy
    obtain ⟨h1, -⟩ := hmem y hy
    have hty' : HasDerivAt (fun y : ℝ ↦ t + y) 1 y := by simpa using (hasDerivAt_id y).const_add t
    refine (((hty'.inv h1.ne').neg).mul_const (1 / (5 * y₀))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z ↦ by simp [one_div]) |>.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 hcont2.intervalIntegrable]
  have hYp : 0 < t + Y := by linarith
  have hlogY : Real.log (Y / (t + Y)) ≤ 0 := Real.log_nonpos (by
    have : 0 < Y := by linarith
    positivity) (by rw [div_le_one hYp]; linarith)
  have hlogY2 : 0 ≤ Real.log (Y / (2 * Real.pi)) / (t + Y) := by
    apply div_nonneg _ hYp.le; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have e : Real.log (y₀ / (t + y₀)) = -Real.log ((t + y₀) / y₀) := by
    rw [← Real.log_inv, inv_div]
  simp only [hG]
  rw [e]
  have : (1 / t) * Real.log (Y / (t + Y)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogY
  have hk : 0 < 1 / (2 * Real.pi) := by positivity
  have : 0 ≤ 1 / (t + Y) * (1 / (5 * y₀)) := by positivity
  have e2 : 1 / (5 * y₀ * (t + y₀)) = 1 / (t + y₀) * (1 / (5 * y₀)) := by field_simp
  have e3 : Real.log (y₀ / (2 * Real.pi)) / (2 * Real.pi * (t + y₀))
      = (1 / (2 * Real.pi)) * (Real.log (y₀ / (2 * Real.pi)) / (t + y₀)) := by field_simp
  have e4 : Real.log ((t + y₀) / y₀) / (2 * Real.pi * t) = (1 / (2 * Real.pi)) * ((1 / t) * Real.log ((t + y₀) / y₀)) := by
    field_simp
  rw [e2, e3, e4]
  nlinarith

/-! ### Numbers for `lem:janframe` -/

theorem zetaNClosed_nonneg (u : ℝ) : 0 ≤ ZeroCount.v1.zetaNClosed u := by
  rcases le_or_gt u 0 with hu | hu
  · have h := CH2Section7A.zsum_one_le (a := 0) (b := u) le_rfl
    unfold ZeroCount.v1.zetaNClosed
    have hempty : IEANTN.zetaZeroesIn Set.univ (Set.Ioc 0 u) = ∅ := by
      ext ρ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, ⟨h1, h2⟩, -⟩; linarith
    unfold IEANTN.zetaZeroesSum; rw [hempty]; simp
  · unfold ZeroCount.v1.zetaNClosed
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := u) le_rfl
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin]
    refine Finset.sum_nonneg fun ρ hρ ↦ ?_
    have := CH2Section7Z.zetaOrder_nonneg_of_mem (J := Set.Ioc 0 u) (fun x hx ↦ hx.1)
      ((Set.Finite.mem_toFinset hfin).mp hρ)
    linarith

theorem log_20_div_le : Real.log (20 / (2 * Real.pi)) ≤ 1.17 := by
  have hπ1 := Real.pi_gt_d6
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hs := CH2Section7A.exp_small_ge (x := 1.17) (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  norm_num at hs
  nlinarith

theorem log_20_div_nonneg : 0 ≤ Real.log (20 / (2 * Real.pi)) :=
  Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_d2])

theorem log_4001_le : Real.log 4001 ≤ 8.3 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (8.3 : ℝ) = (8 : ℕ) + 0.3 by norm_num, Real.exp_add]
  have h8 := (CH2Section7A.exp_nat_bounds 8).1
  have hs := CH2Section7A.exp_small_ge (x := 0.3) (by norm_num)
  have h8' : (2980.9 : ℝ) ≤ Real.exp ((8 : ℕ) : ℝ) := by norm_num at h8 ⊢; linarith
  have hs' : (1.3498 : ℝ) ≤ Real.exp 0.3 := by norm_num at hs ⊢; linarith
  have : (2980.9 : ℝ) * 1.3498 ≤ Real.exp ((8 : ℕ) : ℝ) * Real.exp 0.3 :=
    mul_le_mul h8' hs' (by norm_num) (Real.exp_pos _).le
  linarith

theorem log_51_le : Real.log 51 ≤ 3.94 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (3.94 : ℝ) = (3 : ℕ) + 0.94 by norm_num, Real.exp_add]
  have h3 := (CH2Section7A.exp_nat_bounds 3).1
  have hs := CH2Section7A.exp_small_ge (x := 0.94) (by norm_num)
  have h3' : (20.08 : ℝ) ≤ Real.exp ((3 : ℕ) : ℝ) := by norm_num at h3 ⊢; linarith
  have hs' : (2.55 : ℝ) ≤ Real.exp 0.94 := by norm_num at hs ⊢; linarith
  have : (20.08 : ℝ) * 2.55 ≤ Real.exp ((3 : ℕ) : ℝ) * Real.exp 0.94 :=
    mul_le_mul h3' hs' (by norm_num) (Real.exp_pos _).le
  linarith

theorem zetaN_20_le (hsmall : ZeroCount.v1.rvm_error_small) : ZeroCount.v1.zetaNClosed 20 ≤ 2.42 := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have h := (abs_lt.mp (hsmall 20 (by norm_num) (by norm_num))).2
  have hl := log_20_div_le
  have hl0 := log_20_div_nonneg
  have hM : ZeroCount.v1.rvmMain 20 ≤ 1.42 := by
    unfold ZeroCount.v1.rvmMain
    have hu : 20 / (2 * Real.pi) ≤ 3.1832 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    have hu' : 3.1830 ≤ 20 / (2 * Real.pi) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    nlinarith
  linarith

set_option maxHeartbeats 2000000 in
/-- **`lem:janframe`** for `a = 1/4`, at a finite height `Y`: the zeros right of `t + 1/4`, left of
`t - 1/4`, and (through conjugation) below the real axis. -/
theorem janframe (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    {t Y : ℝ} (ht : 1000 ≤ t) (hY : t + 1 / 4 ≤ Y) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t + 1 / 4) Y) (fun ρ ↦ 1 / (ρ.im - t) ^ 2)
      + IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 (t - 1 / 4)) (fun ρ ↦ 1 / (t - ρ.im) ^ 2)
      + IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 Y) (fun ρ ↦ 1 / (t + ρ.im) ^ 2)
      ≤ 4 / Real.pi * Real.log (t / (2 * Real.pi))
        + 16 * (2 / 5 * Real.log t + 4
          + (ZeroCount.v1.zetaNClosed (t - 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4))
          - (ZeroCount.v1.zetaNClosed (t + 1 / 4) - ZeroCount.v1.rvmMain (t + 1 / 4))) + 0.004 := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  set N := ZeroCount.v1.zetaNClosed
  set M := ZeroCount.v1.rvmMain
  have hN20 := zetaN_20_le hsmall
  -- S1
  have hS1 := lehman_dec hrvm (t₀ := t + (1 / 4)) (t₁ := Y) (φ := fun y ↦ 1 / (y - t) ^ 2)
    (φ' := fun y ↦ -2 / (y - t) ^ 3) (by linarith) hY
    (fun y hy ↦ by
      rw [Set.uIcc_of_le hY] at hy
      have h1 : 0 < y - t := by linarith [hy.1]
      have := ((hasDerivAt_id y).sub_const t).pow 2 |>.inv (by simpa using pow_ne_zero 2 h1.ne')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by simp [one_div])).congr_deriv ?_
      simp only [id, Pi.pow_apply]; field_simp; ring)
    (fun y hy ↦ by
      rw [Set.uIcc_of_le hY] at hy
      have h1 : 0 < y - t := by linarith [hy.1]
      have : (y - t) ^ 3 ≠ 0 := by positivity
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption)))
    (fun y hy ↦ by
      have h1 : 0 < y - t := by linarith [hy.1]
      have : 0 < (y - t) ^ 3 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le)
  have hI1 := integral_right_le (t := t) (a := 1 / 4) (Y := Y) (by nlinarith) (by norm_num) hY
  have hQB : ∀ u : ℝ, 1 ≤ u → |N u - M u| ≤ Real.log u / 5 + 2 := fun u hu ↦ by
    have := hrvm u hu; rwa [show Real.log u / 5 = 1 / 5 * Real.log u by ring]
  have hS1' : IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t + (1 / 4)) Y) (fun ρ ↦ 1 / (ρ.im - t) ^ 2)
      ≤ (Real.log ((t + (1 / 4)) / (2 * Real.pi)) / (2 * Real.pi * (1 / 4)) + Real.log (1 + t / (1 / 4)) / (2 * Real.pi * t)
        + 1 / (5 * t * (1 / 4))) + 16 * ((Real.log (t + (1 / 4)) / 5 + 2) - (N (t + (1 / 4)) - M (t + (1 / 4)))) := by
    have hY1 : 0 ≤ 1 / (Y - t) ^ 2 := by positivity
    have hYQ := (abs_le.mp (hQB Y (by linarith))).2
    have : 1 / (Y - t) ^ 2 * ((N Y - M Y) - (Real.log Y / 5 + 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hY1 (by linarith)
    have e : 1 / (t + (1 / 4) - t) ^ 2 = 16 := by norm_num
    simp only [e] at hS1
    linarith
  -- S2
  rw [CH2Section7A.zsum_split (a := (20:ℝ)) (by norm_num) (by linarith)]
  have hS2a : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 (20:ℝ)) (fun ρ ↦ 1 / (t - ρ.im) ^ 2)
      ≤ 1 / (t - (20:ℝ)) ^ 2 * N (20:ℝ) := by
    have hm := CH2Section7A.zsum_mono (a := 0) (b := (20:ℝ)) le_rfl
      (f := fun ρ ↦ 1 / (t - ρ.im) ^ 2) (g := fun ρ ↦ 1 / (t - (20:ℝ)) ^ 2 * 1) (fun ρ hρ ↦ by
        obtain ⟨-, ⟨h0, h1⟩, -⟩ := hρ
        simp only [mul_one]
        apply one_div_le_one_div_of_le (by nlinarith)
        apply pow_le_pow_left₀ (by linarith) (by linarith) 2)
    rw [CH2Section7A.zsum_const_mul le_rfl] at hm
    exact hm
  have hS2b := lehman_inc hrvm (t₀ := (20:ℝ)) (t₁ := t - (1 / 4)) (φ := fun y ↦ 1 / (t - y) ^ 2)
    (φ' := fun y ↦ 2 / (t - y) ^ 3) (by norm_num) (by linarith)
    (fun y hy ↦ by
      rw [Set.uIcc_of_le (by linarith)] at hy
      have h1 : 0 < t - y := by linarith [hy.2]
      have := ((hasDerivAt_id y).const_sub t).pow 2 |>.inv (by simpa using pow_ne_zero 2 h1.ne')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by simp [one_div])).congr_deriv ?_
      simp only [id, Pi.pow_apply]; field_simp; ring)
    (fun y hy ↦ by
      rw [Set.uIcc_of_le (by linarith)] at hy
      have h1 : 0 < t - y := by linarith [hy.2]
      have : (t - y) ^ 3 ≠ 0 := by positivity
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption)))
    (fun y hy ↦ by
      have h1 : 0 < t - y := by linarith [hy.2]
      positivity)
  have hI2 := integral_left_le (t := t) (a := 1 / 4) (y₀ := 20) (by nlinarith) (by linarith)
    (by norm_num) (by norm_num) (by linarith)
  have hS2b' : IEANTN.zetaZeroesSum Set.univ (Set.Ioc (20:ℝ) (t - (1 / 4))) (fun ρ ↦ 1 / (t - ρ.im) ^ 2)
      ≤ Real.log ((t - (1 / 4)) / (2 * Real.pi)) / (2 * Real.pi * (1 / 4))
        + 16 * ((N (t - (1 / 4)) - M (t - (1 / 4))) + (Real.log (t - (1 / 4)) / 5 + 2)) := by
    have h0 := (abs_le.mp (hQB (20:ℝ) (by norm_num))).1
    have : 0 ≤ 1 / (t - (20:ℝ)) ^ 2 * ((N (20:ℝ) - M (20:ℝ)) + (Real.log (20:ℝ) / 5 + 2)) :=
      mul_nonneg (by positivity) (by linarith)
    have e : 1 / (t - (t - (1 / 4))) ^ 2 = 16 := by norm_num
    simp only [e] at hS2b
    linarith
  -- S4
  rw [CH2Section7A.zsum_split (a := (20:ℝ)) (b := Y) (by norm_num) (by linarith)]
  have hS4a : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 (20:ℝ)) (fun ρ ↦ 1 / (t + ρ.im) ^ 2)
      ≤ 1 / t ^ 2 * N (20:ℝ) := by
    have hm := CH2Section7A.zsum_mono (a := 0) (b := (20:ℝ)) le_rfl
      (f := fun ρ ↦ 1 / (t + ρ.im) ^ 2) (g := fun ρ ↦ 1 / t ^ 2 * 1) (fun ρ hρ ↦ by
        obtain ⟨-, ⟨h0, h1⟩, -⟩ := hρ
        simp only [mul_one]
        apply one_div_le_one_div_of_le (by positivity)
        apply pow_le_pow_left₀ (by linarith) (by linarith) 2)
    rw [CH2Section7A.zsum_const_mul le_rfl] at hm
    exact hm
  have hS4b := lehman_dec hrvm (t₀ := (20:ℝ)) (t₁ := Y) (φ := fun y ↦ 1 / (t + y) ^ 2)
    (φ' := fun y ↦ -2 / (t + y) ^ 3) (by norm_num) (by linarith)
    (fun y hy ↦ by
      rw [Set.uIcc_of_le (by linarith)] at hy
      have h1 : 0 < t + y := by linarith [hy.1]
      have := ((hasDerivAt_id y).const_add t).pow 2 |>.inv (by simpa using pow_ne_zero 2 h1.ne')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by simp [one_div])).congr_deriv ?_
      simp only [id, Pi.pow_apply]; field_simp; ring)
    (fun y hy ↦ by
      rw [Set.uIcc_of_le (by linarith)] at hy
      have h1 : 0 < t + y := by linarith [hy.1]
      have : (t + y) ^ 3 ≠ 0 := by positivity
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption)))
    (fun y hy ↦ by
      have h1 : 0 < t + y := by linarith [hy.1]
      have : 0 < (t + y) ^ 3 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le)
  have hI4 := integral_mirror_le (t := t) (y₀ := 20) (Y := Y) (by nlinarith) (by linarith)
    (by linarith)
  have hS4b' : IEANTN.zetaZeroesSum Set.univ (Set.Ioc (20:ℝ) Y) (fun ρ ↦ 1 / (t + ρ.im) ^ 2)
      ≤ (Real.log ((20:ℝ) / (2 * Real.pi)) / (2 * Real.pi * (t + (20:ℝ)))
        + Real.log ((t + (20:ℝ)) / (20:ℝ)) / (2 * Real.pi * t) + 1 / (5 * (20:ℝ) * (t + (20:ℝ))))
        + 1 / (t + (20:ℝ)) ^ 2 * (2 * (Real.log (20:ℝ) / 5 + 2)) := by
    have hYQ := (abs_le.mp (hQB Y (by linarith))).2
    have h0 := (abs_le.mp (hQB (20:ℝ) (by norm_num))).1
    have : 1 / (t + Y) ^ 2 * ((N Y - M Y) - (Real.log Y / 5 + 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have : 1 / (t + (20:ℝ)) ^ 2 * ((Real.log (20:ℝ) / 5 + 2) - (N (20:ℝ) - M (20:ℝ)))
        ≤ 1 / (t + (20:ℝ)) ^ 2 * (2 * (Real.log (20:ℝ) / 5 + 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  -- the logarithms combine
  have ht4 : 0 < t - 1 / 4 := by linarith
  have hlog2 : Real.log ((t + (1 / 4)) / (2 * Real.pi)) + Real.log ((t - (1 / 4)) / (2 * Real.pi))
      ≤ 2 * Real.log (t / (2 * Real.pi)) := by
    have h1 : 0 < (t + 1 / 4) / (2 * Real.pi) := by positivity
    have h2 : 0 < (t - 1 / 4) / (2 * Real.pi) := by positivity
    rw [← Real.log_mul h1.ne' h2.ne', show 2 * Real.log (t / (2 * Real.pi))
      = Real.log ((t / (2 * Real.pi)) ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    rw [div_mul_div_comm, div_pow, ← pow_two]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hB2 : (Real.log (t + (1 / 4)) / 5 + 2) + (Real.log (t - (1 / 4)) / 5 + 2) ≤ 2 / 5 * Real.log t + 4 := by
    have : Real.log (t + (1 / 4)) + Real.log (t - (1 / 4)) ≤ 2 * Real.log t := by
      rw [← Real.log_mul (by positivity) ht4.ne', show 2 * Real.log t = Real.log (t ^ 2) by
        rw [Real.log_pow]; norm_num]
      apply Real.log_le_log (by positivity)
      nlinarith
    linarith
  -- the small terms
  have hlog4001 := log_4001_le
  have hE1 : Real.log (1 + t / (1 / 4)) / (2 * Real.pi * t) ≤ 0.00133 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Real.log (1 + t / (1 / 4)) ≤ 7.3 + (1 + 4 * t) / 4001 := by
      have e : Real.log (1 + t / (1 / 4)) = Real.log 4001 + Real.log ((1 + 4 * t) / 4001) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
      have := Real.log_le_sub_one_of_pos (show 0 < (1 + 4 * t) / 4001 by positivity)
      linarith
    nlinarith
  have hE2 : 1 / (5 * t * (1 / 4)) ≤ 0.0008 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hE3 : 1 / (t - (20:ℝ)) ^ 2 * N (20:ℝ) ≤ 0.0000026 := by
    have h1 : 1 / (t - (20:ℝ)) ^ 2 ≤ 1 / 960000 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    have hN0 : 0 ≤ N (20:ℝ) := zetaNClosed_nonneg _
    calc _ ≤ 1 / 960000 * 2.42 := mul_le_mul h1 hN20 hN0 (by norm_num)
      _ ≤ 0.0000026 := by norm_num
  have hN0 : 0 ≤ N (20:ℝ) := zetaNClosed_nonneg _
  have hE4 : 1 / t ^ 2 * N (20:ℝ) ≤ 0.0000025 := by
    have h1 : 1 / t ^ 2 ≤ 1 / 1000000 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    calc _ ≤ 1 / 1000000 * 2.42 := mul_le_mul h1 hN20 hN0 (by norm_num)
      _ ≤ 0.0000025 := by norm_num
  have hl20 := log_20_div_le
  have hl20' := log_20_div_nonneg
  have hlog51 := log_51_le
  have hlog20 : Real.log 20 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := (CH2Section7A.exp_nat_bounds 3).1
    norm_num at this ⊢; linarith
  have hE5 : (Real.log ((20:ℝ) / (2 * Real.pi)) / (2 * Real.pi * (t + (20:ℝ)))
        + Real.log ((t + (20:ℝ)) / (20:ℝ)) / (2 * Real.pi * t) + 1 / (5 * (20:ℝ) * (t + (20:ℝ))))
        + 1 / (t + (20:ℝ)) ^ 2 * (2 * (Real.log (20:ℝ) / 5 + 2)) ≤ 0.00084 := by
    have h1 : Real.log (20 / (2 * Real.pi)) / (2 * Real.pi * (t + 20)) ≤ 0.00019 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : Real.log ((t + 20) / 20) / (2 * Real.pi * t) ≤ 0.00063 := by
      have hl : Real.log ((t + 20) / 20) ≤ 2.94 + (t + 20) / 1020 := by
        have e : Real.log ((t + 20) / 20) = Real.log 51 + Real.log ((t + 20) / 1020) := by
          rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp; ring
        have := Real.log_le_sub_one_of_pos (show 0 < (t + 20) / 1020 by positivity)
        linarith
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h3 : 1 / (5 * 20 * (t + 20)) ≤ 0.00001 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h4 : 1 / (t + 20) ^ 2 * (2 * (Real.log 20 / 5 + 2)) ≤ 0.000006 := by
      have hA : 1 / (t + 20) ^ 2 ≤ 1 / 1000000 := by
        apply one_div_le_one_div_of_le (by norm_num); nlinarith
      have hB : 2 * (Real.log 20 / 5 + 2) ≤ 5.2 := by linarith
      have hB0 : 0 ≤ 2 * (Real.log 20 / 5 + 2) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ 20 by norm_num); positivity
      calc _ ≤ 1 / 1000000 * 5.2 := mul_le_mul hA hB hB0 (by norm_num)
        _ ≤ 0.000006 := by norm_num
    linarith
  have hmainlog : Real.log ((t + (1 / 4)) / (2 * Real.pi)) / (2 * Real.pi * (1 / 4))
      + Real.log ((t - (1 / 4)) / (2 * Real.pi)) / (2 * Real.pi * (1 / 4)) ≤ 4 / Real.pi * Real.log (t / (2 * Real.pi)) := by
    have e : Real.log ((t + (1 / 4)) / (2 * Real.pi)) / (2 * Real.pi * (1 / 4))
        + Real.log ((t - (1 / 4)) / (2 * Real.pi)) / (2 * Real.pi * (1 / 4))
        = (2 / Real.pi) * (Real.log ((t + (1 / 4)) / (2 * Real.pi)) + Real.log ((t - (1 / 4)) / (2 * Real.pi))) := by
      field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0:ℝ) ≤ 2 / Real.pi)
    have e2 : 2 / Real.pi * (2 * Real.log (t / (2 * Real.pi))) = 4 / Real.pi * Real.log (t / (2 * Real.pi)) := by
      ring
    linarith
  linarith [hS1', hS2a, hS2b', hS4a, hS4b', hE1, hE2, hE3, hE4, hE5, hmainlog, hB2]

end CH2Section81
