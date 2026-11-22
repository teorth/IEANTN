import TernaryGoldbach.Explicit.GMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# `|Γ(x + iy)| ≤ e^{−φ|y|} Γ(x)/cos^x φ` (`x > 0`, `0 ≤ φ < π/2`)

Substituting `t = u²/2` in the Gamma integral, `G_0(2a − 2) = 2^{a−1} Γ(a)` (`G_δ` from `MellinRotate`),
so the rotation bound for `G_0` with angle `φ/2` is the rotation bound for `Γ` with angle `φ`.
-/

open Complex MeasureTheory Set
open scoped Real

namespace TernaryGoldbach.Explicit

theorem Gr_zero_zero_eq (s : ℂ) (hs : -2 < s.re) :
    Gr s 0 0 = (1 / 2 : ℂ) * (2 : ℂ) ^ ((s + 2) / 2) * Complex.Gamma ((s + 2) / 2) := by
  rw [← mellin_fδ]
  -- `fδ 0 t = t^2 • exp(−t²/2)`
  have e1 : fδ 0 = fun t : ℝ => (t : ℂ) ^ (2 : ℂ) • ((Real.exp (-(t ^ (2 : ℝ)) / 2) : ℝ) : ℂ) := by
    ext t
    simp only [fδ, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, smul_eq_mul,
      Real.rpow_two]
    push_cast
    rw [Complex.cpow_two]
  rw [e1, mellin_cpow_smul, mellin_comp_rpow (fun v : ℝ => ((Real.exp (-v / 2) : ℝ) : ℂ)) _ 2, abs_two]
  have e3 : (fun v : ℝ => ((Real.exp (-v / 2) : ℝ) : ℂ)) =
      fun v => ((Real.exp (-((1 / 2 : ℝ) * v)) : ℝ) : ℂ) := by
    ext v; congr 2; ring
  rw [e3, mellin_comp_mul_left (fun w : ℝ => ((Real.exp (-w) : ℝ) : ℂ)) _ (by norm_num),
    ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral (by simp; linarith)]
  have h2 : ((1 / 2 : ℝ) : ℂ) ^ (-((s + 2) / ((2:ℝ) : ℂ))) = (2 : ℂ) ^ ((s + 2) / 2) := by
    rw [show ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by push_cast; ring,
      Complex.inv_cpow _ _ (by
        have : (2:ℂ).arg = 0 := Complex.arg_eq_zero_iff.2 ⟨by norm_num, by norm_num⟩
        rw [this]; exact Real.pi_ne_zero.symm), Complex.cpow_neg, inv_inv]
    norm_num
  simp only [smul_eq_mul, Complex.real_smul]
  rw [h2]
  push_cast
  ring

/-- **Rotation bound for `Γ`**: `|Γ(x + iy)| ≤ e^{−φ|y|} Γ(x)/cos^x φ` for `x > 0`, `0 ≤ φ < π/2`. -/
theorem norm_Gamma_le_rot {a : ℂ} (ha : 0 < a.re) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ < π / 2) :
    ‖Complex.Gamma a‖ ≤ Real.exp (-(φ * |a.im|)) * Real.Gamma a.re * (Real.cos φ) ^ (-a.re) := by
  set s := 2 * a - 2 with hs
  have hsre : s.re = 2 * a.re - 2 := by simp [hs]
  have hsim : s.im = 2 * a.im := by simp [hs]
  have hs2 : -2 < s.re := by rw [hsre]; linarith
  have hsa : (s + 2) / 2 = a := by rw [hs]; ring
  have hG := Gr_zero_zero_eq s hs2
  rw [hsa] at hG
  have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  set θ : ℝ := if 0 ≤ s.im then φ / 2 else -(φ / 2) with hθ
  have habs : |θ| = φ / 2 := by rw [hθ]; split_ifs <;> simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ φ / 2)]
  have hsg : 0 ≤ θ * s.im := by
    rw [hθ]; split_ifs with h
    · exact mul_nonneg (by linarith) h
    · push Not at h; nlinarith
  have hcos2 : Real.cos (2 * θ) = Real.cos φ := by
    rw [hθ]; split_ifs
    · congr 1; ring
    · rw [show 2 * -(φ / 2) = -φ by ring, Real.cos_neg]
  have hrot := norm_Gr_le s 0 (θ := θ) (by rw [habs]; linarith) hs2 hsg
  rw [habs, hcos2] at hrot
  simp only [abs_zero, mul_zero, zero_mul, add_zero] at hrot
  -- the Gaussian integral is a Gamma value
  have hint := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := s.re + 1) (b := Real.cos φ / 2)
    (by norm_num) (by linarith) (by positivity)
  have e : ∫ r in Ioi (0:ℝ), r ^ (s.re + 1) * Real.exp (-(Real.cos φ / 2) * r ^ 2) =
      ∫ r in Ioi (0:ℝ), r ^ (s.re + 1) * Real.exp (-(Real.cos φ / 2) * r ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [Real.rpow_two]
  rw [e, hint] at hrot
  have hq : (s.re + 1 + 1) / 2 = a.re := by rw [hsre]; ring
  rw [hq, hsim, abs_mul, abs_two] at hrot
  -- `‖G_0(s)‖ = 2^{x−1} ‖Γ(a)‖`
  have h2a : ‖(2:ℂ) ^ a‖ = (2:ℝ) ^ a.re := by
    have := Complex.norm_natCast_cpow_of_pos (by norm_num : 0 < 2) a
    simpa using this
  rw [hG, norm_mul, norm_mul, h2a] at hrot
  have h2x : 0 < (2:ℝ) ^ a.re := by positivity
  have hnorm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hnorm] at hrot
  have hrpow : (Real.cos φ / 2) ^ (-(s.re + 1 + 1) / 2) = (Real.cos φ) ^ (-a.re) * (2:ℝ) ^ a.re := by
    rw [show -(s.re + 1 + 1) / 2 = -a.re by rw [hsre]; ring, Real.div_rpow hcos.le (by norm_num),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul]
  rw [hrpow] at hrot
  have hφe : φ / 2 * (2 * |a.im|) = φ * |a.im| := by ring
  rw [hφe] at hrot
  -- divide by `2^{x}/2`
  have : (1 / 2) * (2:ℝ) ^ a.re * ‖Complex.Gamma a‖ ≤
      (1 / 2) * (2:ℝ) ^ a.re * (Real.exp (-(φ * |a.im|)) * Real.Gamma a.re * (Real.cos φ) ^ (-a.re)) := by
    calc (1 / 2) * (2:ℝ) ^ a.re * ‖Complex.Gamma a‖
        ≤ Real.exp (-(φ * |a.im|)) * ((Real.cos φ) ^ (-a.re) * (2:ℝ) ^ a.re * (1 / 2) * Real.Gamma a.re) :=
          hrot
      _ = _ := by ring
  exact le_of_mul_le_mul_left this (by positivity)

end TernaryGoldbach.Explicit
