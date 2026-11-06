import TernaryGoldbach.Explicit.ZetaPoly
import TernaryGoldbach.Explicit.Digamma

/-!
# Riemann's `ξ`

`ξ(s) = s(s−1)Λ₀(s) + 1` (`Λ₀ = completedRiemannZeta₀`), so that `ξ(s) = s(s−1)π^{−s/2}Γ(s/2)ζ(s)`:
entire, `ξ(1−s) = ξ(s)`, `ξ(s) = s Γℝ(s) (s−1)ζ(s)` for `ℜs > 0`, its zeros are the nontrivial zeros of `ζ`,
`ξ(1/2) ≠ 0`, `ξ'(1/2) = 0`, and `ξ'/ξ = 1/s − ½ log π + ½ ψ(s/2) + ζ'/ζ + 1/(s−1)` for `ℜs > 0`.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace TernaryGoldbach.Explicit

/-- Riemann's `ξ` (without the factor `1/2`). -/
noncomputable def xiF (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xiF : Differentiable ℂ xiF := by
  unfold xiF
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul differentiable_completedZeta₀).add_const 1

theorem xiF_one_sub (s : ℂ) : xiF (1 - s) = xiF s := by
  unfold xiF
  rw [completedRiemannZeta₀_one_sub]; ring

theorem xiF_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : xiF s = s * Gammaℝ s * zetaF s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  rw [zetaF_of_ne hs1, riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq, xiF]
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  field_simp
  ring

theorem xiF_one : xiF 1 = 1 := by simp [xiF]

theorem xiF_zero : xiF 0 = 1 := by simp [xiF]

/-- `ξ(s) ≠ 0` for `ℜs ≥ 1`. -/
theorem xiF_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiF s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [xiF_one]; exact one_ne_zero
  rw [xiF_eq (by linarith) hs1, zetaF_of_ne hs1]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  exact mul_ne_zero (mul_ne_zero hs0 (Gammaℝ_ne_zero_of_re_pos (by linarith)))
    (mul_ne_zero (sub_ne_zero.2 hs1) (riemannZeta_ne_zero_of_one_le_re hs))

/-- `ξ(s) ≠ 0` for `ℜs ≤ 0`. -/
theorem xiF_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : xiF s ≠ 0 := by
  rw [← xiF_one_sub]
  exact xiF_ne_zero_of_one_le_re (by simp; linarith)

/-- In `0 < ℜs < 1`: `ξ(s) = 0 ↔ ζ(s) = 0`. -/
theorem xiF_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : xiF s = 0 ↔ riemannZeta s = 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  rw [xiF_eq h0 hs1, zetaF_of_ne hs1]
  simp [hs0, Gammaℝ_ne_zero_of_re_pos h0, sub_ne_zero.2 hs1]

/-- `ξ'(1/2) = 0`. -/
theorem deriv_xiF_half : deriv xiF (1 / 2) = 0 := by
  have h1 : HasDerivAt xiF (deriv xiF (1 / 2)) (1 / 2) := (differentiable_xiF _).hasDerivAt
  have h2 : HasDerivAt (fun s => xiF (1 - s)) (-deriv xiF (1 / 2)) (1 / 2) := by
    have h3 : HasDerivAt (fun s : ℂ => 1 - s) (-1) (1 / 2) := by
      simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_sub 1
    have h4 : HasDerivAt xiF (deriv xiF (1 - 1 / 2)) (1 - 1 / 2) := (differentiable_xiF _).hasDerivAt
    have := h4.comp (1 / 2 : ℂ) h3
    convert this using 1
    · rfl
    · rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; ring
  have e : (fun s => xiF (1 - s)) = xiF := funext xiF_one_sub
  rw [e] at h2
  have := h1.unique h2
  norm_num at this
  linear_combination this / 2

/-- `ζ(1/2) ≠ 0`, in the form `ℜ zetaF(1/2) ≥ 1/2`. -/
theorem re_zetaF_half_ge : 1 / 2 ≤ (zetaF (1 / 2)).re := by
  have hs : (0:ℝ) < (1 / 2 : ℂ).re := by norm_num
  rw [zetaF_eq hs]
  have hI : (Izeta (1 / 2)).re ≤ 0 := by
    unfold Izeta
    have hint := integrableOn_saw_integrand hs
    rw [show (∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-((1 / 2 : ℂ) + 1))).re =
        RCLike.re (∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-((1 / 2 : ℂ) + 1))) from rfl,
      ← integral_re hint]
    refine setIntegral_nonpos measurableSet_Ioi fun t (ht : 1 < t) => ?_
    have e : (t : ℂ) ^ (-((1 / 2 : ℂ) + 1)) = ((t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith)]; norm_num
    rw [show RCLike.re (saw t * (t : ℂ) ^ (-((1 / 2 : ℂ) + 1))) =
        (saw t * (t : ℂ) ^ (-((1 / 2 : ℂ) + 1))).re from rfl, e, saw, Complex.re_mul_ofReal]
    simp only [Complex.sub_re, Complex.ofReal_re]
    have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    have h2 : 0 < t ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  have e : ((1 / 2 : ℂ) + 1 / 2 * (1 / 2 - 1) * Izeta (1 / 2)).re = 1 / 2 - 1 / 4 * (Izeta (1 / 2)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.div_ofNat_re, Complex.one_re, Complex.sub_re,
      Complex.div_ofNat_im, Complex.one_im, Complex.sub_im]
    norm_num; ring
  rw [e]; linarith

theorem xiF_half_ne_zero : xiF (1 / 2) ≠ 0 := by
  have h1 : (1 / 2 : ℂ) ≠ 1 := by norm_num
  have hs : (0:ℝ) < (1 / 2 : ℂ).re := by norm_num
  rw [xiF_eq hs h1]
  refine mul_ne_zero (mul_ne_zero (by norm_num) (Gammaℝ_ne_zero_of_re_pos hs)) ?_
  intro h
  have := re_zetaF_half_ge
  rw [h] at this; simp at this; linarith

/-- `logDeriv Γℝ(s) = −½ log π + ½ ψ(s/2)` for `ℜs > 0`. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hd1 : HasDerivAt (fun w : ℂ => (π : ℂ) ^ (-w / 2)) ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := by
    have : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact this.const_cpow (Or.inl hpi)
  have hd2 : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hp0 : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hG0 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hm
  have e : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
    ext w; rw [Gammaℝ]
  rw [e, show (fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) =
      (fun w : ℂ => (π : ℂ) ^ (-w / 2)) * (fun w => Complex.Gamma (w / 2)) from rfl,
    logDeriv_mul (f := fun w : ℂ => (π : ℂ) ^ (-w / 2)) (g := fun w => Complex.Gamma (w / 2)) s
    hp0 hG0 hd1.differentiableAt (differentiableAt_Gamma _ hm |>.comp s hd2.differentiableAt),
    hd2.logDeriv_Gamma hm, logDeriv_apply, hd1.deriv]
  field_simp

/-- **`ξ'/ξ = 1/s + Γℝ'/Γℝ + zetaF'/zetaF`** for `ℜs > 0`, `s ≠ 1`, `ξ(s) ≠ 0`. -/
theorem logDeriv_xiF {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hξ : xiF s ≠ 0) :
    logDeriv xiF s = 1 / s + (-(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2)) +
      logDeriv zetaF s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : zetaF s ≠ 0 := by
    intro h; apply hξ; rw [xiF_eq hs hs1, h, mul_zero]
  have hloc : xiF =ᶠ[𝓝 s] fun w => w * Gammaℝ w * zetaF w := by
    have hU : {w : ℂ | 0 < w.re ∧ w ≠ 1} ∈ 𝓝 s :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).mem_nhds ⟨hs, hs1⟩
    filter_upwards [hU] with w hw using xiF_eq hw.1 hw.2
  have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hGd : DifferentiableAt ℂ Gammaℝ s := by
    have e : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
      ext w; rw [Gammaℝ]
    rw [e]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    refine (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)).mul ?_
    exact (differentiableAt_Gamma _ hm).comp s (by fun_prop)
  rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
    show (fun w => w * Gammaℝ w * zetaF w) = (fun w => w * Gammaℝ w) * zetaF from rfl,
    logDeriv_mul (f := fun w => w * Gammaℝ w) (g := zetaF) s (mul_ne_zero hs0 hG) hz
      (differentiableAt_id.mul hGd) (differentiable_zetaF s),
    show (fun w => w * Gammaℝ w) = (fun w : ℂ => w) * Gammaℝ from rfl,
    logDeriv_mul (f := fun w : ℂ => w) (g := Gammaℝ) s hs0 hG differentiableAt_id hGd,
    logDeriv_id', logDeriv_Gammaℝ hs]

end TernaryGoldbach.Explicit
