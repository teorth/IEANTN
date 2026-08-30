/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.CH2.v4.Conclusions
import IEANTN.Nodes.ContourIntegration.v1.Conclusions
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Solution: `CH2.v4`

The whole point of restricting the contour class to L-shaped paths is that the deformation region
is a union of **two rectangles**, so nothing beyond Mathlib's
`integral_boundary_rect_eq_zero_of_differentiableOn` is needed:

* `R₁ = [Re w, 1] × [0, T]`, finite;
* `R₂ = [-M, Re w] × [Im w, T]`, taken to the limit `M → ∞`.

Adding the two boundary identities cancels the shared edge `{Re w} × [Im w, T]`, and the far-left
edge `{-M} × [Im w, T]` vanishes by `DecaysLeft`. What survives is the statement.
-/

open MeasureTheory intervalIntegral Complex Filter Topology

namespace CH2V4Sol

section Helpers

variable {T : ℝ} {f : ℂ → ℂ}

/-- A horizontal segment at height `c ∈ [0, T]`, left of `Re s = 1`, lies in the region. -/
lemma horiz_mem {c x : ℝ} (hc : c ∈ Set.Icc 0 T) (hx : x ≤ 1) :
    (x + c * Complex.I : ℂ) ∈ CH2.v4.UpperRegion T := by
  constructor <;> simp [hx, hc.1, hc.2]

/-- A vertical segment at abscissa `c ≤ 1` lies in the region. -/
lemma vert_mem {c y : ℝ} (hc : c ≤ 1) (hy : y ∈ Set.Icc 0 T) :
    (c + y * Complex.I : ℂ) ∈ CH2.v4.UpperRegion T := by
  constructor <;> simp [hc, hy.1, hy.2]

lemma cont (hdiff : DifferentiableOn ℂ f (CH2.v4.UpperRegion T)) :
    ContinuousOn f (CH2.v4.UpperRegion T) := hdiff.continuousOn

/-- Interval integrability along a horizontal segment inside the region. -/
lemma horiz_integrable (hdiff : DifferentiableOn ℂ f (CH2.v4.UpperRegion T))
    {c u v : ℝ} (hc : c ∈ Set.Icc 0 T) (huv : ∀ x ∈ Set.uIcc u v, x ≤ 1) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + c * Complex.I)) volume u v := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.comp (cont hdiff) (by fun_prop) ?_
  intro x hx
  exact horiz_mem hc (huv x hx)

/-- Interval integrability along a vertical segment inside the region. -/
lemma vert_integrable (hdiff : DifferentiableOn ℂ f (CH2.v4.UpperRegion T))
    {c u v : ℝ} (hc : c ≤ 1) (huv : ∀ y ∈ Set.uIcc u v, y ∈ Set.Icc 0 T) :
    IntervalIntegrable (fun y : ℝ ↦ f (c + y * Complex.I)) volume u v := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.comp (cont hdiff) (by fun_prop) ?_
  intro y hy
  exact vert_mem hc (huv y hy)

/-- Integrability along any continuous segment that stays inside the punctured region. -/
lemma seg_integrable {P : Finset ℂ} {g : ℝ → ℂ}
    (hdiff : DifferentiableOn ℂ f (CH2.v4.UpperRegion T \ ↑P)) (hg : Continuous g) {u v : ℝ}
    (hmem : ∀ t ∈ Set.uIcc u v, g t ∈ CH2.v4.UpperRegion T \ ↑P) :
    IntervalIntegrable (fun t : ℝ ↦ f (g t)) volume u v :=
  ContinuousOn.intervalIntegrable
    (ContinuousOn.comp hdiff.continuousOn hg.continuousOn hmem)

/-- The far-left edge vanishes as `M → ∞`: `DecaysLeft` bounds `‖f‖` by `ε` on `Re s ≤ -M`, and
the edge has length `T - b`. -/
lemma tendsto_left_edge {b : ℝ} (hb0 : 0 ≤ b) (hbT : b ≤ T)
    (hdecay : CH2.v4.DecaysLeft T f) :
    Tendsto (fun M : ℝ ↦ ∫ y : ℝ in b..T, f (-M + y * Complex.I)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hdecay (ε / (2 * (T - b + 1))) (by positivity)
  refine ⟨max M₀ 1, fun M hM ↦ ?_⟩
  have hM0 : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hbound : ∀ y ∈ Set.uIoc b T, ‖f (-M + y * Complex.I)‖ ≤ ε / (2 * (T - b + 1)) := by
    intro y hy
    rw [Set.uIoc_of_le hbT] at hy
    refine hM₀ _ ?_ ?_
    · simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_mul, sub_zero,
        add_zero, sub_self]
      linarith
    · simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add, neg_zero,
        add_zero, Set.mem_Icc]
      constructor <;> linarith [hy.1, hy.2]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := T)
    (C := ε / (2 * (T - b + 1))) hbound
  rw [dist_zero_right]
  refine lt_of_le_of_lt hle ?_
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ T - b), div_mul_eq_mul_div,
    div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (T - b + 1))]
  nlinarith [hε]

end Helpers

end CH2V4Sol

open CH2V4Sol in
theorem CH2.v4.challenge_contour_shift_holomorphic : CH2.v4.contour_shift_holomorphic := by
  intro T w f hT hw1 hwim hdiff hdecay hray htop
  obtain ⟨hb0, hbT⟩ := hwim
  set a : ℝ := w.re with hadef
  set b : ℝ := w.im with hbdef
  have hb0' : (0:ℝ) ≤ b := le_of_lt hb0
  have hbT' : b ≤ T := le_of_lt hbT
  -- ### Rectangle 1: `[a, 1] × [0, T]`
  have R1 : (∫ x : ℝ in a..1, f x) - (∫ x : ℝ in a..1, f (x + T * Complex.I))
      + Complex.I * (∫ y : ℝ in (0:ℝ)..T, f (1 + y * Complex.I))
      - Complex.I * (∫ y : ℝ in (0:ℝ)..T, f (a + y * Complex.I)) = 0 := by
    have hsub : (Set.uIcc a (1:ℝ) ×ℂ Set.uIcc (0:ℝ) T) ⊆ CH2.v4.UpperRegion T := by
      rintro s hs
      rw [Complex.mem_reProdIm] at hs
      rw [Set.uIcc_of_le hw1] at hs
      rw [Set.uIcc_of_le hT.le] at hs
      exact ⟨hs.1.2, hs.2⟩
    have := integral_boundary_rect_eq_zero_of_differentiableOn f ((a : ℂ)) ((1:ℝ) + T * Complex.I)
      (hdiff.mono (by simpa using hsub))
    simpa [smul_eq_mul] using this
  -- ### Rectangle 2: `[-M, a] × [b, T]`, for every `M` with `-M ≤ a`
  have R2 : ∀ M : ℝ, -M ≤ a →
      (∫ x : ℝ in (-M)..a, f (x + b * Complex.I))
        - (∫ x : ℝ in (-M)..a, f (x + T * Complex.I))
        + Complex.I * (∫ y : ℝ in b..T, f (a + y * Complex.I))
        - Complex.I * (∫ y : ℝ in b..T, f (-M + y * Complex.I)) = 0 := by
    intro M hM
    have hsub : (Set.uIcc (-M) a ×ℂ Set.uIcc b T) ⊆ CH2.v4.UpperRegion T := by
      rintro s hs
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hM, Set.uIcc_of_le hbT'] at hs
      exact ⟨le_trans hs.1.2 hw1, ⟨le_trans hb0' hs.2.1, hs.2.2⟩⟩
    have := integral_boundary_rect_eq_zero_of_differentiableOn f
      ((-M : ℝ) + b * Complex.I) ((a : ℝ) + T * Complex.I) (hdiff.mono (by simpa using hsub))
    simpa [smul_eq_mul] using this
  -- ### Interval additivity, to merge the shared edges
  have hadd_top : ∀ M : ℝ, -M ≤ a →
      (∫ x : ℝ in (-M)..a, f (x + T * Complex.I)) + (∫ x : ℝ in a..(1:ℝ), f (x + T * Complex.I))
        = ∫ x : ℝ in (-M)..(1:ℝ), f (x + T * Complex.I) := by
    intro M hM
    refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
    · exact horiz_integrable hdiff ⟨hT.le, le_refl T⟩ (fun x hx ↦ by
        rw [Set.uIcc_of_le hM] at hx; exact le_trans hx.2 hw1)
    · exact horiz_integrable hdiff ⟨hT.le, le_refl T⟩ (fun x hx ↦ by
        rw [Set.uIcc_of_le hw1] at hx; exact hx.2)
  have hadd_vert : (∫ y : ℝ in (0:ℝ)..b, f (a + y * Complex.I))
      + (∫ y : ℝ in b..T, f (a + y * Complex.I))
      = ∫ y : ℝ in (0:ℝ)..T, f (a + y * Complex.I) := by
    refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
    · exact vert_integrable hdiff hw1 (fun y hy ↦ by
        rw [Set.uIcc_of_le hb0'] at hy; exact ⟨hy.1, le_trans hy.2 hbT'⟩)
    · exact vert_integrable hdiff hw1 (fun y hy ↦ by
        rw [Set.uIcc_of_le hbT'] at hy; exact ⟨le_trans hb0' hy.1, hy.2⟩)
  -- ### The combined identity, for every large `M`
  set E : ℝ → ℂ := fun M ↦
    (∫ x : ℝ in a..1, f x)
      + Complex.I * (∫ y : ℝ in (0:ℝ)..T, f (1 + y * Complex.I))
      - Complex.I * (∫ y : ℝ in (0:ℝ)..b, f (a + y * Complex.I))
      + (∫ x : ℝ in (-M)..a, f (x + b * Complex.I))
      - (∫ x : ℝ in (-M)..(1:ℝ), f (x + T * Complex.I))
      - Complex.I * (∫ y : ℝ in b..T, f (-M + y * Complex.I)) with hEdef
  have hE : ∀ M : ℝ, -M ≤ a → E M = 0 := by
    intro M hM
    have h2 := R2 M hM
    have h3 := hadd_top M hM
    rw [hEdef]
    simp only
    linear_combination R1 + h2 + h3 - Complex.I * hadd_vert
  -- ### Pass to the limit
  have hlimit : Tendsto E atTop (𝓝 (
      (∫ x : ℝ in a..1, f x)
        + Complex.I * (∫ y : ℝ in (0:ℝ)..T, f (1 + y * Complex.I))
        - Complex.I * (∫ y : ℝ in (0:ℝ)..b, f (a + y * Complex.I))
        + (∫ x : ℝ in Set.Iic a, f (x + b * Complex.I))
        - (∫ x : ℝ in Set.Iic (1:ℝ), f (x + T * Complex.I))
        - Complex.I * 0)) := by
    rw [hEdef]
    exact (((tendsto_const_nhds.add tendsto_const_nhds).sub tendsto_const_nhds).add
        (intervalIntegral_tendsto_integral_Iic a hray tendsto_neg_atTop_atBot)).sub
        (intervalIntegral_tendsto_integral_Iic (1:ℝ) htop tendsto_neg_atTop_atBot) |>.sub
      (tendsto_const_nhds.mul (tendsto_left_edge hb0' hbT' hdecay))
  have hzero : Tendsto E atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (-a)] with M hM
    exact (hE M (by linarith)).symm
  have hkey := tendsto_nhds_unique hlimit hzero
  -- ### Rearrange
  rw [CH2.v4.lContourIntegral]
  have hrev : (∫ x : ℝ in (1:ℝ)..a, f x) = -(∫ x : ℝ in a..1, f x) :=
    intervalIntegral.integral_symm a 1
  linear_combination hkey - hrev

open CH2V4Sol in
/-- The general shift. The only thing this needs beyond the pole-free case is the residue theorem,
which Mathlib does not have and which arrives as the imported hypothesis.

The decomposition is cut at the HORIZONTAL line `Im s = Im w`, not the vertical one used above, and
that is the whole trick: `[-M, 1] × [Im w, T]` then holds *every* pole -- the statement's
`Im w + r < ρ.im` guarantees it -- and `[Re w, 1] × [0, Im w]` holds none, so the import is used
exactly once and Mathlib's own theorem covers the rest. -/
theorem CH2.v4.challenge_contour_shift
    (contourintegration_v1_residue_theorem_rectangle :
      ContourIntegration.v1.residue_theorem_rectangle) : CH2.v4.contour_shift := by
  intro T r w P f hT hr hw1 hwim hP hdisj hdiff hdecay hray htop
  obtain ⟨hb0, hbT⟩ := hwim
  set a : ℝ := w.re with hadef
  set b : ℝ := w.im with hbdef
  have hb0' : (0:ℝ) ≤ b := le_of_lt hb0
  have hbT' : b ≤ T := le_of_lt hbT
  -- Every pole sits strictly above the ray, so the lower rectangle is pole-free.
  have hPabove : ∀ ρ ∈ P, b < ρ.im := fun ρ hρ ↦ by linarith [(hP ρ hρ).1, hr]
  -- ### The small rectangle `[a, 1] × [0, b]`: no poles, so Mathlib suffices.
  have SMALL : (∫ x : ℝ in a..1, f x) - (∫ x : ℝ in a..1, f (x + b * Complex.I))
      + Complex.I * (∫ y : ℝ in (0:ℝ)..b, f (1 + y * Complex.I))
      - Complex.I * (∫ y : ℝ in (0:ℝ)..b, f (a + y * Complex.I)) = 0 := by
    have hsub : (Set.uIcc a (1:ℝ) ×ℂ Set.uIcc (0:ℝ) b) ⊆ CH2.v4.UpperRegion T \ ↑P := by
      rintro s hs
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hw1, Set.uIcc_of_le hb0'] at hs
      refine ⟨⟨hs.1.2, ⟨hs.2.1, le_trans hs.2.2 hbT'⟩⟩, ?_⟩
      intro hmem
      exact absurd hs.2.2 (not_le.mpr (hPabove s (by exact_mod_cast hmem)))
    have := integral_boundary_rect_eq_zero_of_differentiableOn f ((a : ℂ))
      ((1:ℝ) + b * Complex.I) (hdiff.mono (by simpa using hsub))
    simpa [smul_eq_mul] using this
  -- ### The big rectangle `[-M, 1] × [b, T]`: holds every pole.
  obtain ⟨M₀, hM₀⟩ := (P.image (fun ρ : ℂ ↦ r - ρ.re)).exists_le
  have BIG : ∀ M : ℝ, M₀ < M → -M < 1 →
      (∫ x : ℝ in (-M)..1, f (x + b * Complex.I))
        - (∫ x : ℝ in (-M)..1, f (x + T * Complex.I))
        + Complex.I * (∫ y : ℝ in b..T, f (1 + y * Complex.I))
        - Complex.I * (∫ y : ℝ in b..T, f (-M + y * Complex.I))
        = ∑ ρ ∈ P, (∮ ζ in C(ρ, r), f ζ) := by
    intro M hMbig hM1
    have hsub : (Set.uIcc (-M) (1:ℝ) ×ℂ Set.uIcc b T) ⊆ CH2.v4.UpperRegion T := by
      rintro s hs
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hM1.le, Set.uIcc_of_le hbT'] at hs
      exact ⟨hs.1.2, ⟨le_trans hb0' hs.2.1, hs.2.2⟩⟩
    have := contourintegration_v1_residue_theorem_rectangle ((-M : ℝ) + b * Complex.I) ((1:ℝ) + T * Complex.I) P r f
      (by simpa using hM1) (by simpa using hbT) hr
      (by
        intro ρ hρ
        obtain ⟨h1, h2, h3⟩ := hP ρ hρ
        have hlow : r - ρ.re ≤ M₀ := hM₀ _ (Finset.mem_image_of_mem _ hρ)
        refine ⟨by simpa using (by linarith : -M < ρ.re - r), by simpa using h3,
          by simpa using (by linarith : b < ρ.im - r), by simpa using h2⟩)
      hdisj
      (hdiff.mono (by
        intro s hs
        exact ⟨hsub (by simpa using hs.1), hs.2⟩))
    simpa [smul_eq_mul] using this
  -- ### Additivity, to merge the two shared edges
  have hadd_horiz : ∀ M : ℝ, -M ≤ a →
      (∫ x : ℝ in (-M)..a, f (x + b * Complex.I)) + (∫ x : ℝ in a..(1:ℝ), f (x + b * Complex.I))
        = ∫ x : ℝ in (-M)..(1:ℝ), f (x + b * Complex.I) := by
    intro M hM
    have hseg : ∀ u v : ℝ, (∀ x ∈ Set.uIcc u v, x ≤ 1) →
        IntervalIntegrable (fun x : ℝ ↦ f (x + b * Complex.I)) volume u v := by
      intro u v huv
      refine seg_integrable hdiff (by fun_prop) (fun x hx ↦ ⟨horiz_mem ⟨hb0', hbT'⟩ (huv x hx), ?_⟩)
      intro hmem
      have := hPabove _ (by exact_mod_cast hmem)
      simp at this
    refine intervalIntegral.integral_add_adjacent_intervals
      (hseg _ _ fun x hx ↦ ?_) (hseg _ _ fun x hx ↦ ?_)
    · rw [Set.uIcc_of_le hM] at hx; exact le_trans hx.2 hw1
    · rw [Set.uIcc_of_le hw1] at hx; exact hx.2
  have hadd_vert : (∫ y : ℝ in (0:ℝ)..b, f (1 + y * Complex.I))
      + (∫ y : ℝ in b..T, f (1 + y * Complex.I))
      = ∫ y : ℝ in (0:ℝ)..T, f (1 + y * Complex.I) := by
    have hseg : ∀ u v : ℝ, (∀ y ∈ Set.uIcc u v, y ∈ Set.Icc 0 T) →
        IntervalIntegrable (fun y : ℝ ↦ f (1 + y * Complex.I)) volume u v := by
      intro u v huv
      refine seg_integrable hdiff (by fun_prop) (fun y hy ↦ ⟨vert_mem le_rfl (huv y hy), ?_⟩)
      intro hmem
      have := (hP _ (by exact_mod_cast hmem)).2.2
      simp at this
      linarith
    refine intervalIntegral.integral_add_adjacent_intervals (hseg _ _ fun y hy ↦ ?_)
      (hseg _ _ fun y hy ↦ ?_)
    · rw [Set.uIcc_of_le hb0'] at hy; exact ⟨hy.1, le_trans hy.2 hbT'⟩
    · rw [Set.uIcc_of_le hbT'] at hy; exact ⟨le_trans hb0' hy.1, hy.2⟩
  -- ### The combined identity, for every large `M`
  set E : ℝ → ℂ := fun M ↦
    (∫ x : ℝ in a..1, f x)
      + Complex.I * (∫ y : ℝ in (0:ℝ)..T, f (1 + y * Complex.I))
      - Complex.I * (∫ y : ℝ in (0:ℝ)..b, f (a + y * Complex.I))
      + (∫ x : ℝ in (-M)..a, f (x + b * Complex.I))
      - (∫ x : ℝ in (-M)..(1:ℝ), f (x + T * Complex.I))
      - Complex.I * (∫ y : ℝ in b..T, f (-M + y * Complex.I))
      - ∑ ρ ∈ P, (∮ ζ in C(ρ, r), f ζ) with hEdef
  have hE : ∀ M : ℝ, M₀ < M → -M ≤ a → -M < 1 → E M = 0 := by
    intro M hM0 hMa hM1
    have hbig := BIG M hM0 hM1
    have hh := hadd_horiz M hMa
    rw [hEdef]
    simp only
    linear_combination hbig + SMALL + hh - Complex.I * hadd_vert
  -- ### Pass to the limit
  have hlimit : Tendsto E atTop (𝓝 (
      (∫ x : ℝ in a..1, f x)
        + Complex.I * (∫ y : ℝ in (0:ℝ)..T, f (1 + y * Complex.I))
        - Complex.I * (∫ y : ℝ in (0:ℝ)..b, f (a + y * Complex.I))
        + (∫ x : ℝ in Set.Iic a, f (x + b * Complex.I))
        - (∫ x : ℝ in Set.Iic (1:ℝ), f (x + T * Complex.I))
        - Complex.I * 0
        - ∑ ρ ∈ P, (∮ ζ in C(ρ, r), f ζ))) := by
    rw [hEdef]
    exact ((((tendsto_const_nhds.add tendsto_const_nhds).sub tendsto_const_nhds).add
        (intervalIntegral_tendsto_integral_Iic a hray tendsto_neg_atTop_atBot)).sub
        (intervalIntegral_tendsto_integral_Iic (1:ℝ) htop tendsto_neg_atTop_atBot) |>.sub
      (tendsto_const_nhds.mul (tendsto_left_edge hb0' hbT' hdecay))).sub tendsto_const_nhds
  have hzero : Tendsto E atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop M₀, eventually_ge_atTop (-a), eventually_gt_atTop (-1:ℝ)]
      with M h1 h2 h3
    exact (hE M h1 (by linarith) (by linarith)).symm
  have hkey := tendsto_nhds_unique hlimit hzero
  -- ### Rearrange
  rw [CH2.v4.lContourIntegral]
  have hrev : (∫ x : ℝ in (1:ℝ)..a, f x) = -(∫ x : ℝ in a..1, f x) :=
    intervalIntegral.integral_symm a 1
  linear_combination hkey - hrev
