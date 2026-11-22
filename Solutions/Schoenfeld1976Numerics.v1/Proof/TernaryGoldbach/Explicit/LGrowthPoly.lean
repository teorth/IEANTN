import TernaryGoldbach.Explicit.GammaBounds
import TernaryGoldbach.Explicit.LGrowthLeft

/-!
# Polynomial growth of `L(s, χ)` on `−8 ≤ ℜs ≤ 1/4`

`L(1 − s, χ) = q^{s−1/2} ε Γℝ(s+κ) L(s, χ⁻¹) / Γℝ(1−s+κ)`. Bounding `|Γℝ(s+κ)|` by the rotation bound
and `|1/Γℝ(1−s+κ)| = π^{…}|Γ(1−w)| |sin πw|/π` (reflection) also by the rotation bound, both with angle
`π/2 − 1/(|t|+1)`, the factors `e^{∓π|t|/4}` and `|sin| ≤ e^{π|t|/2}` cancel up to `e`:
`|L(z, χ)| ≤ C_q (|ℑz| + 1)^{10} (|ℑz| + 9)`.
-/

open Complex MeasureTheory Set
open scoped Real

namespace TernaryGoldbach.Explicit

theorem sin_ge_four_fifths {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : 4 / 5 * ε ≤ Real.sin ε := by
  have h := Real.sin_bound (x := ε) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at h
  have := (abs_le.1 h).1
  have h2 : ε ^ 2 ≤ 1 := by nlinarith
  have h3 : ε ^ 3 ≤ ε := by nlinarith
  have h5 : ε ^ 5 ≤ ε := by nlinarith [pow_nonneg h0 4]
  nlinarith

/-- The angle `φ_t = π/2 − 1/(|t|+1)`: `cos φ_t ≥ 4/(5(|t|+1))`, `e^{(π/2 − φ_t)|t|} ≤ e`. -/
theorem angle_facts (t : ℝ) :
    0 ≤ π / 2 - 1 / (|t| + 1) ∧ π / 2 - 1 / (|t| + 1) < π / 2 ∧
      4 / (5 * (|t| + 1)) ≤ Real.cos (π / 2 - 1 / (|t| + 1)) ∧
      (π / 2 - (π / 2 - 1 / (|t| + 1))) * |t| ≤ 1 := by
  have ht : 0 < |t| + 1 := by positivity
  have hε0 : 0 < 1 / (|t| + 1) := by positivity
  have hε1 : 1 / (|t| + 1) ≤ 1 := by rw [div_le_one ht]; linarith [abs_nonneg t]
  refine ⟨by linarith [Real.pi_gt_three], by linarith, ?_, ?_⟩
  · rw [Real.cos_pi_div_two_sub]
    have := sin_ge_four_fifths hε0.le hε1
    calc 4 / (5 * (|t| + 1)) = 4 / 5 * (1 / (|t| + 1)) := by field_simp
      _ ≤ _ := this
  · rw [show π / 2 - (π / 2 - 1 / (|t| + 1)) = 1 / (|t| + 1) by ring]
    rw [div_mul_eq_mul_div, one_mul, div_le_one ht]; linarith

/-- `cos^{−a} φ_t ≤ (1.25(|t|+1))^a` for `a ≥ 0`. -/
theorem cos_rpow_neg_le (t : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (Real.cos (π / 2 - 1 / (|t| + 1))) ^ (-a) ≤ (1.25 * (|t| + 1)) ^ a := by
  obtain ⟨-, -, hcos, -⟩ := angle_facts t
  have ht : 0 < |t| + 1 := by positivity
  have hc0 : 0 < 4 / (5 * (|t| + 1)) := by positivity
  rw [Real.rpow_neg (by linarith), ← Real.inv_rpow (by linarith)]
  refine Real.rpow_le_rpow (inv_nonneg.2 (by linarith)) ?_ ha
  rw [inv_le_comm₀ (by linarith) (by positivity)]
  calc (1.25 * (|t| + 1))⁻¹ = 4 / (5 * (|t| + 1)) := by field_simp; norm_num
    _ ≤ _ := hcos

/-- `|1/Γ(w)| ≤ (1/π) e^{π|ℑw|} |Γ(1−w)|` (reflection), `−4 ≤ ℜw ≤ 5/8`. -/
theorem norm_inv_Gamma_le_refl {w : ℂ} (h1 : -4 ≤ w.re) (h2 : w.re ≤ 5 / 8) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ 1 / π * Real.exp (π * |w.im|) * ‖Complex.Gamma (1 - w)‖ := by
  by_cases hΓ : Complex.Gamma w = 0
  · rw [hΓ, inv_zero, norm_zero]; positivity
  have hre1 : 0 < (1 - w).re := by simp; linarith
  have hΓ1 : Complex.Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre1
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hsin : Complex.sin (π * w) ≠ 0 := by
    intro h; rw [h, div_zero] at hrefl; exact mul_ne_zero hΓ hΓ1 hrefl
  have e : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (π * w) / π := by
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    rw [show Complex.Gamma w * Complex.Gamma (1 - w) * Complex.sin (w * π) =
      (Complex.Gamma w * Complex.Gamma (1 - w)) * Complex.sin (π * w) by ring, hrefl]
    field_simp
  have hsinb : ‖Complex.sin (π * w)‖ ≤ Real.exp (π * |w.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin (π * w)‖ / π
      ≤ ‖Complex.Gamma (1 - w)‖ * Real.exp (π * |w.im|) / π := by gcongr
    _ = 1 / π * Real.exp (π * |w.im|) * ‖Complex.Gamma (1 - w)‖ := by ring

/-- `|Γℝ(s')| ≤ 24 e^{−φ_t |t|/2} (1.25(|t|+1))^5` for `3/4 ≤ ℜs' ≤ 10`, `|ℑs'| = |t|`. -/
theorem norm_Gammaℝ_le_poly {s' : ℂ} (h1 : 3 / 4 ≤ s'.re) (h2 : s'.re ≤ 10) :
    ‖Gammaℝ s'‖ ≤ 24 * Real.exp (-((π / 2 - 1 / (|s'.im| + 1)) * |s'.im| / 2)) *
      (1.25 * (|s'.im| + 1)) ^ (5 : ℝ) := by
  obtain ⟨hφ0, hφ, -, -⟩ := angle_facts s'.im
  rw [Gammaℝ_def, norm_mul, norm_cpow_pi]
  have hre : (s' / 2).re = s'.re / 2 := by simp
  have him : (s' / 2).im = s'.im / 2 := by simp
  have hG := norm_Gamma_le_rot (a := s' / 2) (by rw [hre]; linarith) hφ0 hφ
  rw [hre, him, abs_div, abs_two] at hG
  have hpi : π ^ (-s' / 2).re ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith
  have hΓ : Real.Gamma (s'.re / 2) ≤ 24 := Gamma_le_24 (by linarith) (by linarith)
  have hc := cos_rpow_neg_le s'.im (a := s'.re / 2) (by linarith)
  have hc' : (1.25 * (|s'.im| + 1)) ^ (s'.re / 2) ≤ (1.25 * (|s'.im| + 1)) ^ (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [abs_nonneg s'.im]) (by linarith)
  have hexp : Real.exp (-((π / 2 - 1 / (|s'.im| + 1)) * (|s'.im| / 2))) =
      Real.exp (-((π / 2 - 1 / (|s'.im| + 1)) * |s'.im| / 2)) := by ring_nf
  rw [hexp] at hG
  have hΓ0 : 0 ≤ Real.Gamma (s'.re / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  calc π ^ (-s' / 2).re * ‖Complex.Gamma (s' / 2)‖
      ≤ 1 * (Real.exp (-((π / 2 - 1 / (|s'.im| + 1)) * |s'.im| / 2)) * Real.Gamma (s'.re / 2) *
          (Real.cos (π / 2 - 1 / (|s'.im| + 1))) ^ (-(s'.re / 2))) :=
        mul_le_mul hpi hG (norm_nonneg _) (by norm_num)
    _ ≤ 1 * (Real.exp (-((π / 2 - 1 / (|s'.im| + 1)) * |s'.im| / 2)) * 24 *
          (1.25 * (|s'.im| + 1)) ^ (5 : ℝ)) := by
        have hcp : 0 ≤ (Real.cos (π / 2 - 1 / (|s'.im| + 1))) ^ (-(s'.re / 2)) :=
          Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le (by positivity) (angle_facts s'.im).2.2.1)) _
        have he := Real.exp_pos (-((π / 2 - 1 / (|s'.im| + 1)) * |s'.im| / 2))
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hΓ he.le) (hc.trans hc') hcp (by positivity)
    _ = _ := by ring

theorem pi_rpow_le_208 {x : ℝ} (hx : x ≤ 5 / 8) : π ^ x ≤ 0.48⁻¹ := by
  have : π ^ x ≤ π ^ (5 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hx
  refine this.trans ?_
  have hx0 : 0 ≤ π ^ (5 / 8 : ℝ) := by positivity
  have h8 : (π ^ (5 / 8 : ℝ)) ^ 8 = π ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num
  have h5 : π ^ 5 ≤ (0.48⁻¹ : ℝ) ^ 8 := by
    have := Real.pi_lt_d2
    calc π ^ 5 ≤ 3.15 ^ 5 := pow_le_pow_left₀ Real.pi_pos.le this.le 5
      _ ≤ (0.48⁻¹ : ℝ) ^ 8 := by norm_num
  rw [← h8] at h5
  exact (pow_le_pow_iff_left₀ hx0 (by norm_num) (by norm_num : (8:ℕ) ≠ 0)).1 h5

/-- `|1/Γℝ(w')| ≤ (24/(0.48π)) e^{π|t|/2} e^{−φ_t|t|/2} (1.25(|t|+1))^5`, `t = ℑw'`, `−8 ≤ ℜw' ≤ 5/4`. -/
theorem norm_inv_Gammaℝ_le_poly {w' : ℂ} (h1 : -8 ≤ w'.re) (h2 : w'.re ≤ 5 / 4) :
    ‖(Gammaℝ w')⁻¹‖ ≤ 24 / (0.48 * π) * Real.exp (π * |w'.im| / 2) *
      Real.exp (-((π / 2 - 1 / (|w'.im| + 1)) * |w'.im| / 2)) * (1.25 * (|w'.im| + 1)) ^ (5 : ℝ) := by
  obtain ⟨hφ0, hφ, -, -⟩ := angle_facts w'.im
  rw [Gammaℝ_def, mul_inv, norm_mul, ← Complex.cpow_neg, norm_cpow_pi]
  have hre : (w' / 2).re = w'.re / 2 := by simp
  have him : (w' / 2).im = w'.im / 2 := by simp
  have hpi : π ^ (-(-w' / 2)).re ≤ 0.48⁻¹ := pi_rpow_le_208 (by simp; linarith)
  have hR := norm_inv_Gamma_le_refl (w := w' / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [him, abs_div, abs_two] at hR
  have hre1 : (1 - w' / 2).re = 1 - w'.re / 2 := by simp
  have him1 : (1 - w' / 2).im = -(w'.im / 2) := by simp
  have hG := norm_Gamma_le_rot (a := 1 - w' / 2) (by rw [hre1]; linarith) hφ0 hφ
  rw [hre1, him1, abs_neg, abs_div, abs_two] at hG
  have hΓ : Real.Gamma (1 - w'.re / 2) ≤ 24 := Gamma_le_24 (by linarith) (by linarith)
  have hc := cos_rpow_neg_le w'.im (a := 1 - w'.re / 2) (by linarith)
  have hc' : (1.25 * (|w'.im| + 1)) ^ (1 - w'.re / 2) ≤ (1.25 * (|w'.im| + 1)) ^ (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [abs_nonneg w'.im]) (by linarith)
  have hcp : 0 ≤ (Real.cos (π / 2 - 1 / (|w'.im| + 1))) ^ (-(1 - w'.re / 2)) :=
    Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le (by positivity) (angle_facts w'.im).2.2.1)) _
  have hΓ0 : 0 ≤ Real.Gamma (1 - w'.re / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hexp1 : Real.exp (π * (|w'.im| / 2)) = Real.exp (π * |w'.im| / 2) := by ring_nf
  have hexp2 : Real.exp (-((π / 2 - 1 / (|w'.im| + 1)) * (|w'.im| / 2))) =
      Real.exp (-((π / 2 - 1 / (|w'.im| + 1)) * |w'.im| / 2)) := by ring_nf
  rw [hexp1] at hR; rw [hexp2] at hG
  have hGb : ‖Complex.Gamma (1 - w' / 2)‖ ≤ Real.exp (-((π / 2 - 1 / (|w'.im| + 1)) * |w'.im| / 2)) * 24 *
      (1.25 * (|w'.im| + 1)) ^ (5 : ℝ) := by
    refine hG.trans ?_
    have he := Real.exp_pos (-((π / 2 - 1 / (|w'.im| + 1)) * |w'.im| / 2))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hΓ he.le) (hc.trans hc') hcp (by positivity)
  have hpos : 0 ≤ 1 / π * Real.exp (π * |w'.im| / 2) := by positivity
  calc π ^ (-(-w' / 2)).re * ‖(Complex.Gamma (w' / 2))⁻¹‖
      ≤ 0.48⁻¹ * (1 / π * Real.exp (π * |w'.im| / 2) * ‖Complex.Gamma (1 - w' / 2)‖) :=
        mul_le_mul hpi hR (norm_nonneg _) (by norm_num)
    _ ≤ 0.48⁻¹ * (1 / π * Real.exp (π * |w'.im| / 2) *
          (Real.exp (-((π / 2 - 1 / (|w'.im| + 1)) * |w'.im| / 2)) * 24 *
            (1.25 * (|w'.im| + 1)) ^ (5 : ℝ))) := by
        gcongr
    _ = _ := by field_simp

/-- **Polynomial growth on the left**: for `χ` primitive, `χ ≠ 1`, `−8 ≤ ℜz ≤ 1/4`:
`|L(z, χ)| ≤ 1400 q⁹ (q + 1)(|ℑz| + 9)(1.25(|ℑz| + 1))^{10}`. -/
theorem norm_LFunction_left_poly {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {z : ℂ} (h1 : -8 ≤ z.re) (h2 : z.re ≤ 1 / 4) :
    ‖χ.LFunction z‖ ≤ 1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|z.im| + 9) *
      (1.25 * (|z.im| + 1)) ^ (10 : ℝ) := by
  have hN : N ≠ 1 := by
    rintro rfl; exact hχ1 (Subsingleton.elim _ _)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set s := 1 - z with hs
  have hz : z = 1 - s := by rw [hs]; ring
  have hsre : s.re = 1 - z.re := by simp [hs]
  have hsim : s.im = -z.im := by simp [hs]
  have hσ1 : 3 / 4 ≤ s.re := by rw [hsre]; linarith
  have hσ2 : s.re ≤ 9 := by rw [hsre]; linarith
  have hχi : χ⁻¹ ≠ 1 := fun h => hχ1 (inv_eq_one.1 h)
  set t := |z.im| with ht
  set φ := π / 2 - 1 / (t + 1) with hφ
  obtain ⟨-, -, -, hφt⟩ := angle_facts z.im
  set P := (1.25 * (t + 1)) ^ (5 : ℝ) with hP
  have hGs : ‖DirichletCharacter.gammaFactor χ⁻¹ s‖ ≤ 24 * Real.exp (-(φ * t / 2)) * P := by
    rcases χ⁻¹.even_or_odd with he | ho
    · rw [he.gammaFactor_def]
      have := norm_Gammaℝ_le_poly (s' := s) hσ1 (by linarith)
      rwa [hsim, abs_neg] at this
    · rw [ho.gammaFactor_def]
      have := norm_Gammaℝ_le_poly (s' := s + 1) (by simp; linarith) (by simp; linarith)
      have e : (s + 1).im = -z.im := by simp [hsim]
      rwa [e, abs_neg] at this
  have hΛ : DirichletCharacter.completedLFunction χ⁻¹ s =
      DirichletCharacter.gammaFactor χ⁻¹ s * χ⁻¹.LFunction s := by
    have hGs0 : DirichletCharacter.gammaFactor χ⁻¹ s ≠ 0 := by
      rcases χ⁻¹.even_or_odd with he | ho
      · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by linarith)
      · rw [ho.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inr hN)]
    field_simp
  have hG1 : ‖(DirichletCharacter.gammaFactor χ (1 - s))⁻¹‖ ≤
      24 / (0.48 * π) * Real.exp (π * t / 2) * Real.exp (-(φ * t / 2)) * P := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def, ← hz]; exact norm_inv_Gammaℝ_le_poly h1 (by linarith)
    · rw [ho.gammaFactor_def, ← hz]
      have := norm_inv_Gammaℝ_le_poly (w' := z + 1) (by simp; linarith) (by simp; linarith)
      have e : (z + 1).im = z.im := by simp
      rwa [e] at this
  have hL : χ.LFunction z = (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
      (DirichletCharacter.gammaFactor χ⁻¹ s * χ⁻¹.LFunction s) *
        (DirichletCharacter.gammaFactor χ (1 - s))⁻¹ := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN), hz,
      hχ.completedLFunction_one_sub s, hΛ, div_eq_mul_inv]
  rw [hL, norm_mul, norm_mul, norm_mul, norm_mul, norm_rootNumber hχ, mul_one,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))]
  have hNp : (N : ℝ) ^ (s - 1 / 2).re ≤ (N : ℝ) ^ 9 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by simp; push_cast; linarith)
  have hLs : ‖χ⁻¹.LFunction s‖ ≤ ((N : ℝ) + 1) * (t + 9) / (3 / 4) := by
    refine (norm_LFunction_le hχi (by linarith)).trans ?_
    have hsn : ‖s‖ ≤ t + 9 := by
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [hsim, abs_neg, abs_of_pos (by linarith : (0:ℝ) < s.re)]; linarith
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsn (by positivity)) (by norm_num) hσ1
  have hexp : Real.exp (-(φ * t / 2)) * (Real.exp (π * t / 2) * Real.exp (-(φ * t / 2))) ≤ Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have hφt' : (π / 2 - φ) * t ≤ 1 := hφt
    exact Real.exp_le_exp.2 (by linarith)
  have he1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have hP0 : 0 ≤ P := by positivity
  have hPP : P * P = (1.25 * (t + 1)) ^ (10 : ℝ) := by
    rw [hP, ← Real.rpow_add (by positivity)]; norm_num
  have hpi := Real.pi_gt_d2
  have hc : 24 * (24 / (0.48 * π)) * Real.exp 1 ≤ 1040 := by
    rw [div_eq_mul_inv]
    have : (0.48 * π)⁻¹ ≤ (0.48 * 3.14)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith [Real.exp_pos 1]
  calc (N : ℝ) ^ (s - 1 / 2).re * (‖DirichletCharacter.gammaFactor χ⁻¹ s‖ * ‖χ⁻¹.LFunction s‖) *
        ‖(DirichletCharacter.gammaFactor χ (1 - s))⁻¹‖
      ≤ (N : ℝ) ^ 9 * ((24 * Real.exp (-(φ * t / 2)) * P) * (((N : ℝ) + 1) * (t + 9) / (3 / 4))) *
          (24 / (0.48 * π) * Real.exp (π * t / 2) * Real.exp (-(φ * t / 2)) * P) := by
        gcongr
    _ = (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (t + 9) * (4 / 3) * (24 * (24 / (0.48 * π))) *
          (Real.exp (-(φ * t / 2)) * (Real.exp (π * t / 2) * Real.exp (-(φ * t / 2)))) * (P * P) := by
        ring
    _ ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (t + 9) * (4 / 3) * (24 * (24 / (0.48 * π))) *
          Real.exp 1 * (P * P) := by gcongr
    _ ≤ 1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (t + 9) * (1.25 * (t + 1)) ^ (10 : ℝ) := by
        rw [hPP]
        have hA : 0 ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (t + 9) * (1.25 * (t + 1)) ^ (10 : ℝ) := by positivity
        nlinarith

end TernaryGoldbach.Explicit
