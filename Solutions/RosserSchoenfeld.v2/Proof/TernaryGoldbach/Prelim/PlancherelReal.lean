import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Plancherel for `L¹ ∩ L²` functions on `ℝ`

Mathlib has the `L²` Fourier transform (`MeasureTheory.Lp.fourierTransformₗᵢ`, `Lp.norm_fourier_eq`). For
`f ∈ L¹ ∩ L²` we identify it a.e. with the integral `𝓕 f`: both define the same tempered distribution
(`Lp.fourier_toTemperedDistribution_eq` and `VectorFourier.integral_fourierIntegral_smul_eq_flip`), and
`ae_eq_zero_of_integral_contDiff_smul_eq_zero` concludes. Hence `∫ |𝓕 f|² = ∫ |f|²`.
-/

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap

namespace TernaryGoldbach

theorem innerₗ_real_flip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
  ext; simp

/-- For `f ∈ L¹ ∩ L²`, the `L²` Fourier transform of `f` is the integral `𝓕 f` a.e. -/
theorem fourierL2_ae_eq {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    ((𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := h2.toLp f with hF
  set G : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 F with hG
  have hFf : (F : ℝ → ℂ) =ᵐ[volume] f := h2.coeFn_toLp
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) h1
  have hloc : LocallyIntegrable (fun x => (G : ℝ → ℂ) x - 𝓕 f x) volume :=
    ((Lp.memLp G).locallyIntegrable (by norm_num)).sub hcont.locallyIntegrable
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • ((G : ℝ → ℂ) x - 𝓕 f x) = 0 := by
    intro g hg hgc
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    set g' := hg₁.toSchwartzMap hg₂ with hg'
    have hg'g : ∀ x, g' x = (g x : ℂ) := fun x => rfl
    -- `∫ g G = ∫ (𝓕 g') f`
    have e1 : ∫ x, g' x • (G : ℝ → ℂ) x = ∫ x, (𝓕 g') x • f x := by
      have h := congrArg (fun T : 𝓢'(ℝ, ℂ) => T g') (Lp.fourier_toTemperedDistribution_eq F)
      simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h
      rw [← h]
      exact integral_congr_ae (hFf.mono fun x hx => by simp only; rw [hx])
    -- `∫ (𝓕 g') f = ∫ g' (𝓕 f)`
    have e2 : ∫ x, (𝓕 g') x • f x = ∫ x, g' x • 𝓕 f x := by
      have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
        (L := innerₗ ℝ) (e := 𝐞) (f := (g' : ℝ → ℂ)) (g := f) Real.continuous_fourierChar
        (by fun_prop) (g'.integrable) h1
      rw [innerₗ_real_flip] at this
      exact this
    have hIG : Integrable (fun x => g' x • (G : ℝ → ℂ) x) := by
      simp only [smul_eq_mul]
      exact (g'.memLp 2 volume).integrable_mul (Lp.memLp G)
    have hIF : Integrable (fun x => g' x • 𝓕 f x) := by
      refine Integrable.mono' (g'.integrable.norm.mul_const (∫ x, ‖f x‖))
        ((g'.continuous.smul hcont).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (Real.norm_fourier_le_integral_norm f x) (norm_nonneg _)
    have e3 : ∫ x, g x • ((G : ℝ → ℂ) x - 𝓕 f x) =
        (∫ x, g' x • (G : ℝ → ℂ) x) - ∫ x, g' x • 𝓕 f x := by
      have hfun : (fun x => g x • ((G : ℝ → ℂ) x - 𝓕 f x)) =
          fun x => g' x • (G : ℝ → ℂ) x - g' x • 𝓕 f x := by
        funext x; rw [hg'g, smul_sub, Complex.real_smul, Complex.real_smul]; rfl
      rw [hfun]; exact integral_sub hIG hIF
    rw [e3]
    exact sub_eq_zero.2 (e1.trans e2)
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc key
  exact this.mono fun x hx => sub_eq_zero.1 hx

theorem L2_norm_sq_eq (H : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖H‖ ^ 2 = ∫ x, ‖(H : ℝ → ℂ) x‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) H H
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have h' : ((∫ x, ‖(H : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) = ∫ x, ((‖(H : ℝ → ℂ) x‖ : ℂ)) ^ 2 := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  have h'' : ((‖H‖ ^ 2 : ℝ) : ℂ) = ((∫ x, ‖(H : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h.trans h'.symm
  exact_mod_cast h''

/-- **Plancherel for `L¹ ∩ L²` on `ℝ`**: `∫ |𝓕 f|² = ∫ |f|²`. -/
theorem integral_norm_sq_fourier {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := h2.toLp f with hF
  have hG := fourierL2_ae_eq h1 h2
  have hFf : (F : ℝ → ℂ) =ᵐ[volume] f := h2.coeFn_toLp
  calc ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ ξ, ‖((𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 :=
        integral_congr_ae (hG.mono fun ξ h => by simp only; rw [h])
    _ = ‖(𝓕 F : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 := (L2_norm_sq_eq _).symm
    _ = ‖F‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖(F : ℝ → ℂ) x‖ ^ 2 := L2_norm_sq_eq _
    _ = ∫ x, ‖f x‖ ^ 2 := integral_congr_ae (hFf.mono fun x h => by simp only; rw [h])

/-- `𝓕 f ∈ L²` for `f ∈ L¹ ∩ L²`. -/
theorem memLp_fourier {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))).ae_eq (fourierL2_ae_eq h1 h2)

end TernaryGoldbach
