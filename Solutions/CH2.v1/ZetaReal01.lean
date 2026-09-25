/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Convex
import Section7

/-!
# `ζ` has no zeros in `[0, 1)`

Mathlib's `riemannZeta₀ s = ζ(s) - 1/(s-1)` is entire, and `ZetaAsymptotics.zeta_limit_aux1` gives
`riemannZeta₀ s = 1 - s ∫_1^∞ {x} x^{-s-1} dx` for real `s > 1`. The integral is the Mellin transform
of `{x}·1_{x>1}` at `-s`, holomorphic on `Re s > 0`, so by the identity theorem the formula holds
there. For `0 < s < 1` it reads `ζ(s) = s/(s-1) - s ∫_1^∞ {x} x^{-s-1} dx < 0`; and `ζ(0) = -1/2`.
-/

open Complex Real MeasureTheory Filter Topology Set

namespace CH2ZetaReal

/-- `{t} · 1_{t > 1}`. -/
noncomputable def gfr (t : ℝ) : ℂ := (Ioi (1:ℝ)).indicator (fun t ↦ ((Int.fract t : ℝ) : ℂ)) t

/-- `J(s) = ∫_1^∞ {t} t^{-s-1} dt`, as a Mellin transform. -/
noncomputable def Jz (s : ℂ) : ℂ := mellin gfr (-s)

theorem norm_gfr_le (t : ℝ) : ‖gfr t‖ ≤ 1 := by
  unfold gfr
  by_cases h : t ∈ Ioi (1:ℝ)
  · rw [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  · rw [indicator_of_notMem h, norm_zero]; norm_num

theorem measurable_gfr : Measurable gfr :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi

theorem locallyIntegrableOn_gfr : LocallyIntegrableOn gfr (Ioi 0) := by
  intro x _
  refine ⟨Ioo (x - 1) (x + 1), nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  exact IntegrableOn.of_bound (by simp) measurable_gfr.aestronglyMeasurable 1
    (Eventually.of_forall norm_gfr_le)

theorem differentiableAt_Jz {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Jz s := by
  have htop : gfr =O[atTop] (fun t : ℝ ↦ t ^ (-(0:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact norm_gfr_le t
  have hbot : gfr =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-(-s.re - 1))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
    rw [gfr, indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact ht.2.le), norm_zero]
    positivity
  have h := mellin_differentiableAt_of_isBigO_rpow (s := -s) locallyIntegrableOn_gfr htop
    (by simp; linarith) hbot (by simp)
  exact h.comp s differentiableAt_id.neg

/-- For real `s`, `J` is the real integral. -/
theorem Jz_ofReal (s : ℝ) :
    Jz (s : ℂ) = ((∫ t in Ioi (1:ℝ), t ^ (-s - 1) * Int.fract t : ℝ) : ℂ) := by
  rw [Jz, mellin]
  have h1 : (∫ t in Ioi (0:ℝ), (t : ℂ) ^ (-(s : ℂ) - 1) • gfr t)
      = ∫ t in Ioi (0:ℝ), (Ioi (1:ℝ)).indicator
          (fun t ↦ (((t ^ (-s - 1) * Int.fract t : ℝ)) : ℂ)) t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : (0:ℝ) < t := ht
    by_cases h : t ∈ Ioi (1:ℝ)
    · rw [gfr, indicator_of_mem h, indicator_of_mem h, smul_eq_mul]
      push_cast
      rw [Complex.ofReal_cpow ht0.le]
      push_cast; ring
    · rw [gfr, indicator_of_notMem h, indicator_of_notMem h, smul_zero]
  rw [h1, setIntegral_indicator measurableSet_Ioi,
    show Ioi (0:ℝ) ∩ Ioi 1 = Ioi 1 by
      ext t; simp only [mem_inter_iff, mem_Ioi]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨by linarith, h⟩⟩]
  exact integral_ofReal

/-- For real `s > 1`, `J(s)` is `ZetaAsymptotics.termTSum s`. -/
theorem integral_fract_eq_termTSum {s : ℝ} (hs : 1 < s) :
    (∫ t in Ioi (1:ℝ), t ^ (-s - 1) * Int.fract t) = ZetaAsymptotics.termTSum s := by
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (-s - 1) * Int.fract t) (Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) one_pos)
      ?_ ?_
    · exact ((measurable_id.pow_const _).mul measurable_fract).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
        abs_of_nonneg (Int.fract_nonneg t)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg ht0.le _) (Int.fract_lt_one t).le
  have hlim := intervalIntegral_tendsto_integral_Ioi 1 hint
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  -- the partial integrals are the partial sums
  have hpart : ∀ N : ℕ, (∫ t in (1:ℝ)..((N : ℝ) + 1), t ^ (-s - 1) * Int.fract t)
      = ZetaAsymptotics.termSum s N := by
    intro N
    have hadj := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun t : ℝ ↦ t ^ (-s - 1) * Int.fract t) (μ := volume) (a := fun k : ℕ ↦ (k : ℝ) + 1)
      (n := N) (fun k _ ↦ ?_)
    · simp only [Nat.cast_zero, zero_add] at hadj
      rw [← hadj, ZetaAsymptotics.termSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [ZetaAsymptotics.term]
      have hne : ∀ᵐ t : ℝ ∂volume, t ≠ (k : ℝ) + 1 + 1 := by
        rw [ae_iff]; simp
      push_cast
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne] with t htne ht
      rw [uIoc_of_le (by linarith)] at ht
      have hfl : Int.floor t = (k : ℤ) + 1 := by
        rw [Int.floor_eq_iff]; push_cast
        exact ⟨ht.1.le, lt_of_le_of_ne ht.2 (by push_cast at htne; exact htne)⟩
      have ht0 : (0:ℝ) < t := by
        have := ht.1; have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
      rw [Int.fract, hfl]
      push_cast
      rw [show -s - 1 = -(s + 1) by ring, Real.rpow_neg ht0.le]
      ring
    · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)).mpr
        (hint.mono_set fun t ht ↦ ?_)
      have := ht.1
      simp only [mem_Ioi]
      push_cast at this
      linarith
  have ht : Tendsto (fun N : ℕ ↦ ZetaAsymptotics.termSum s N) atTop
      (𝓝 (∫ t in Ioi (1:ℝ), t ^ (-s - 1) * Int.fract t)) := by
    refine hlim.congr fun N ↦ ?_
    exact hpart N
  have hsum : HasSum (fun n : ℕ ↦ ZetaAsymptotics.term (n + 1) s)
      (∫ t in Ioi (1:ℝ), t ^ (-s - 1) * Int.fract t) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) s) _).mpr ht
  rw [ZetaAsymptotics.termTSum, hsum.tsum_eq]

/-- **`riemannZeta₀ s = 1 - s J(s)` on `Re s > 0`.** -/
theorem riemannZeta₀_eq {s : ℂ} (hs : 0 < s.re) : riemannZeta₀ s = 1 - s * Jz s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ riemannZeta₀ U :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun z ↦ 1 - z * Jz z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hUo
    exact (DifferentiableAt.sub (differentiableAt_const _) (differentiableAt_id.mul
      (differentiableAt_Jz hz))).differentiableWithinAt
  have hreal : ∀ r : ℝ, 1 < r → riemannZeta₀ (r : ℂ) = 1 - (r : ℂ) * Jz r := by
    intro r hr
    have hr1 : (r : ℂ) ≠ 1 := by exact_mod_cast hr.ne'
    have hz := riemannZeta_eq_inv_sub_add hr1
    rw [CH2Section7.zeta_ofReal hr] at hz
    have haux := ZetaAsymptotics.zeta_limit_aux1 hr
    rw [Jz_ofReal, integral_fract_eq_termTSum hr]
    have e : riemannZeta₀ (r : ℂ) = ((CH2Section7.zetaReal r - 1 / (r - 1) : ℝ) : ℂ) := by
      rw [eq_sub_of_add_eq' hz.symm]
      push_cast; ring
    rw [e, CH2Section7.zetaReal, haux]
    push_cast; ring
  have hfreq : ∃ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ), riemannZeta₀ z = 1 - z * Jz z := by
    have hu : Tendsto (fun n : ℕ ↦ (((3 / 2 + 1 / ((n : ℝ) + 2)) : ℝ) : ℂ)) atTop
        (𝓝[≠] ((3 / 2 : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have h1 : Tendsto (fun n : ℕ ↦ (3 / 2 + 1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 (3 / 2 + 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop))
        rw [add_zero] at h1
        exact (Complex.continuous_ofReal.tendsto _).comp h1
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h' := Complex.ofReal_injective h
        have : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    refine hu.frequently (Frequently.of_forall fun n ↦ ?_)
    exact hreal _ (by have : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
                      linarith)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    (show ((3 / 2 : ℝ) : ℂ) ∈ U by simp [hU]) hfreq hs

/-- **`ζ(s) ≠ 0` for real `s ∈ [0, 1)`.** -/
theorem riemannZeta_ne_zero_Ico {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : riemannZeta (s : ℂ) ≠ 0 := by
  rcases h0.eq_or_lt with rfl | hpos
  · rw [Complex.ofReal_zero, riemannZeta_zero]; norm_num
  have hs1 : (s : ℂ) ≠ 1 := by exact_mod_cast h1.ne
  rw [riemannZeta_eq_inv_sub_add hs1, riemannZeta₀_eq (by simpa using hpos), Jz_ofReal]
  set Jr := ∫ t in Ioi (1:ℝ), t ^ (-s - 1) * Int.fract t with hJr
  have hJ0 : 0 ≤ Jr := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    exact mul_nonneg (Real.rpow_nonneg ht0.le _) (Int.fract_nonneg t)
  have e : ((s : ℂ) - 1)⁻¹ + (1 - (s : ℂ) * (Jr : ℂ)) = (((s - 1)⁻¹ + 1 - s * Jr : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.ofReal_ne_zero]
  have hneg : (s - 1)⁻¹ + 1 < 0 := by
    have : (s - 1)⁻¹ < -1 := by
      rw [inv_eq_one_div, div_lt_iff_of_neg (by linarith)]; linarith
    linarith
  have : 0 ≤ s * Jr := mul_nonneg hpos.le hJ0
  linarith

end CH2ZetaReal
