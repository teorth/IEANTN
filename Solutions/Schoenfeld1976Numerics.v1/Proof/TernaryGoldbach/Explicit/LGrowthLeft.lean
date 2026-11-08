import TernaryGoldbach.Explicit.LGrowth
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Growth of `L(s, χ)` for `ℜs ≤ 1/4` (`χ` primitive, `≠ 1`)

From the functional equation `Λ(1 − s, χ) = q^{s−1/2} ε Λ(s, χ⁻¹)`, `Λ(s, χ) = Γℝ(s + κ) L(s, χ)`:
`|L(1 − s, χ)| = q^{σ−1/2} π^{1/2−σ} |Γ((s+κ)/2)| / |Γ((1−s+κ)/2)| · |L(s, χ⁻¹)|`. The numerator is at
most `Γ(ℜ)` (the Gamma integral), and the reflection formula bounds the denominator below by
`π e^{−π|t|/2}/24`. The resulting bound grows like `e^{π|t|/2}`, which is all that is needed.
-/

open Complex MeasureTheory Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : (0:ℝ) < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx']
  simp

theorem Gamma_le_one_of_mem {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have h := Real.convexOn_Gamma.le_max_of_mem_segment (x := 1) (y := 2) (z := x)
    (by norm_num) (by norm_num) (by rw [segment_eq_Icc (by norm_num)]; exact ⟨h1, h2⟩)
  rw [Real.Gamma_one, Real.Gamma_two, max_self] at h
  exact h

theorem Gamma_le_24 {x : ℝ} (h1 : 3 / 8 ≤ x) (h2 : x ≤ 5) : Real.Gamma x ≤ 24 := by
  have h38 : Real.Gamma (3 / 8) ≤ 8 / 3 := by
    have e := Real.Gamma_add_one (s := 3 / 8) (by norm_num)
    have h := Gamma_le_one_of_mem (x := 3 / 8 + 1) (by norm_num) (by norm_num)
    rw [e] at h
    nlinarith
  have h5 : Real.Gamma 5 = 24 := by
    rw [show (5:ℝ) = ((4:ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have h := Real.convexOn_Gamma.le_max_of_mem_segment (x := 3 / 8) (y := 5) (z := x)
    (by norm_num) (by norm_num) (by rw [segment_eq_Icc (by norm_num)]; exact ⟨h1, h2⟩)
  rw [h5] at h
  exact h.trans (max_le (by linarith) le_rfl)

theorem norm_sin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h : ‖Complex.sin w‖ ≤ (Real.exp w.im + Real.exp (-w.im)) / 2 := by
    rw [Complex.sin, norm_div, norm_mul]
    simp only [Complex.norm_I, mul_one, Complex.norm_ofNat]
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.norm_exp]
    simp [Complex.mul_re, add_comm]
  refine h.trans ?_
  rcases le_total 0 w.im with hw | hw
  · rw [abs_of_nonneg hw]
    have := Real.exp_le_exp.2 (show -w.im ≤ w.im by linarith); linarith
  · rw [abs_of_nonpos hw]
    have := Real.exp_le_exp.2 (show w.im ≤ -w.im by linarith); linarith

/-- `|Γ(w)| ≥ π e^{−π|ℑw|}/24` for `−4 ≤ ℜw ≤ 5/8`, `ℑw ≠ 0`. -/
theorem norm_Gamma_ge {w : ℂ} (h1 : -4 ≤ w.re) (h2 : w.re ≤ 5 / 8) (him : w.im ≠ 0) :
    π * Real.exp (-(π * |w.im|)) / 24 ≤ ‖Complex.Gamma w‖ := by
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hsin : Complex.sin (π * w) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.intCast_re, Complex.intCast_im, mul_zero] at this
    exact him ((mul_eq_zero.1 this).resolve_left Real.pi_ne_zero)
  have hre1 : 0 < (1 - w).re := by simp; linarith
  have hG1 : ‖Complex.Gamma (1 - w)‖ ≤ 24 :=
    (norm_Gamma_le_Gamma_re hre1).trans (Gamma_le_24 (by simp; linarith) (by simp; linarith))
  have hsinb : ‖Complex.sin (π * w)‖ ≤ Real.exp (π * |w.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have hprod : ‖Complex.Gamma w‖ * ‖Complex.Gamma (1 - w)‖ = π / ‖Complex.sin (π * w)‖ := by
    rw [← norm_mul, hrefl, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hs0 : 0 < ‖Complex.sin (π * w)‖ := norm_pos_iff.2 hsin
  have hG1pos : 0 < ‖Complex.Gamma (1 - w)‖ := by
    rcases (norm_nonneg (Complex.Gamma (1 - w))).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hprod
      exact absurd hprod.symm (div_ne_zero Real.pi_ne_zero hs0.ne')
  have e1 : ‖Complex.Gamma w‖ = π / (‖Complex.sin (π * w)‖ * ‖Complex.Gamma (1 - w)‖) := by
    rw [div_mul_eq_div_div, ← hprod]; field_simp
  rw [e1]
  have hden : ‖Complex.sin (π * w)‖ * ‖Complex.Gamma (1 - w)‖ ≤ 24 * Real.exp (π * |w.im|) := by
    have := mul_le_mul hsinb hG1 hG1pos.le (Real.exp_pos _).le
    linarith
  calc π * Real.exp (-(π * |w.im|)) / 24 = π / (24 * Real.exp (π * |w.im|)) := by
        rw [Real.exp_neg]; field_simp
    _ ≤ π / (‖Complex.sin (π * w)‖ * ‖Complex.Gamma (1 - w)‖) :=
        div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hden

/-! ## The gamma factors -/

theorem norm_cpow_pi (s : ℂ) : ‖(π : ℂ) ^ s‖ = π ^ s.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]

/-- `|Γℝ(s)| ≤ 24` for `3/4 ≤ ℜs ≤ 9`... and for `ℜs + 1` in the same range. -/
theorem norm_Gammaℝ_le {s : ℂ} (h1 : 3 / 4 ≤ s.re) (h2 : s.re ≤ 10) : ‖Gammaℝ s‖ ≤ 24 := by
  rw [Gammaℝ_def, norm_mul, norm_cpow_pi]
  have hre : (s / 2).re = s.re / 2 := by simp
  have hpi : π ^ (-s / 2).re ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith
  have hG : ‖Complex.Gamma (s / 2)‖ ≤ 24 :=
    (norm_Gamma_le_Gamma_re (by rw [hre]; linarith)).trans (Gamma_le_24 (by rw [hre]; linarith)
      (by rw [hre]; linarith))
  calc π ^ (-s / 2).re * ‖Complex.Gamma (s / 2)‖ ≤ 1 * 24 :=
        mul_le_mul hpi hG (norm_nonneg _) (by norm_num)
    _ = 24 := by ring

/-- `|Γℝ(w)| ≥ 0.0628 e^{−π|ℑw|/2}` for `−8 ≤ ℜw ≤ 5/4`, `ℑw ≠ 0`. -/
theorem norm_Gammaℝ_ge {w : ℂ} (h1 : -8 ≤ w.re) (h2 : w.re ≤ 5 / 4) (him : w.im ≠ 0) :
    0.0628 * Real.exp (-(π * |w.im| / 2)) ≤ ‖Gammaℝ w‖ := by
  rw [Gammaℝ_def, norm_mul, norm_cpow_pi]
  have hre : (w / 2).re = w.re / 2 := by simp
  have him2 : (w / 2).im = w.im / 2 := by simp
  have hG := norm_Gamma_ge (w := w / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him2]; exact div_ne_zero him two_ne_zero)
  rw [him2, abs_div, abs_two] at hG
  have hpi : 0.48 ≤ π ^ (-w / 2).re := by
    have he : (-w / 2).re = -(w.re / 2) := by simp; ring
    rw [he]
    have : π ^ (-(5 / 8 : ℝ)) ≤ π ^ (-(w.re / 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    refine le_trans ?_ this
    rw [Real.rpow_neg Real.pi_pos.le, le_inv_comm₀ (by norm_num) (by positivity)]
    have hx : 0 ≤ π ^ (5 / 8 : ℝ) := by positivity
    have h8 : (π ^ (5 / 8 : ℝ)) ^ 8 = π ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num
    have h5 : π ^ 5 ≤ (0.48⁻¹ : ℝ) ^ 8 := by
      have := Real.pi_lt_d2
      calc π ^ 5 ≤ 3.15 ^ 5 := pow_le_pow_left₀ Real.pi_pos.le this.le 5
        _ ≤ (0.48⁻¹ : ℝ) ^ 8 := by norm_num
    rw [← h8] at h5
    exact (pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (8:ℕ) ≠ 0)).1 h5
  have hpi3 := Real.pi_gt_d2
  have e : π * |w.im| / 2 = π * (|w.im| / 2) := by ring
  rw [e]
  calc 0.0628 * Real.exp (-(π * (|w.im| / 2)))
      ≤ 0.48 * (π * Real.exp (-(π * (|w.im| / 2))) / 24) := by
        have := Real.exp_pos (-(π * (|w.im| / 2)))
        nlinarith
    _ ≤ π ^ (-w / 2).re * ‖Complex.Gamma (w / 2)‖ :=
        mul_le_mul hpi hG (by positivity) (by positivity)

/-- `|1/Γ(w)| ≤ (24/π) e^{π|ℑw|}` for `−4 ≤ ℜw ≤ 5/8` (reflection; also at the poles). -/
theorem norm_inv_Gamma_le {w : ℂ} (h1 : -4 ≤ w.re) (h2 : w.re ≤ 5 / 8) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ 24 / π * Real.exp (π * |w.im|) := by
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
  have hG1 : ‖Complex.Gamma (1 - w)‖ ≤ 24 :=
    (norm_Gamma_le_Gamma_re hre1).trans (Gamma_le_24 (by simp; linarith) (by simp; linarith))
  have hsinb : ‖Complex.sin (π * w)‖ ≤ Real.exp (π * |w.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [div_le_iff₀ Real.pi_pos]
  calc ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin (π * w)‖ ≤ 24 * Real.exp (π * |w.im|) :=
        mul_le_mul hG1 hsinb (norm_nonneg _) (by norm_num)
    _ = 24 / π * Real.exp (π * |w.im|) * π := by field_simp

/-- `|1/Γℝ(w)| ≤ 16 e^{π|ℑw|/2}` for `−8 ≤ ℜw ≤ 5/4`. -/
theorem norm_inv_Gammaℝ_le {w : ℂ} (h1 : -8 ≤ w.re) (h2 : w.re ≤ 5 / 4) :
    ‖(Gammaℝ w)⁻¹‖ ≤ 16 * Real.exp (π * |w.im| / 2) := by
  rw [Gammaℝ_def, mul_inv, norm_mul, ← Complex.cpow_neg, norm_cpow_pi]
  have hre : (w / 2).re = w.re / 2 := by simp
  have him2 : (w / 2).im = w.im / 2 := by simp
  have hG := norm_inv_Gamma_le (w := w / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [him2, abs_div, abs_two] at hG
  have hpi : π ^ (-(-w / 2)).re ≤ 0.48⁻¹ := by
    have he : (-(-w / 2)).re = w.re / 2 := by simp; ring
    rw [he]
    have : π ^ (w.re / 2) ≤ π ^ (5 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    refine this.trans ?_
    have hx : 0 ≤ π ^ (5 / 8 : ℝ) := by positivity
    have h8 : (π ^ (5 / 8 : ℝ)) ^ 8 = π ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num
    have h5 : π ^ 5 ≤ (0.48⁻¹ : ℝ) ^ 8 := by
      have := Real.pi_lt_d2
      calc π ^ 5 ≤ 3.15 ^ 5 := pow_le_pow_left₀ Real.pi_pos.le this.le 5
        _ ≤ (0.48⁻¹ : ℝ) ^ 8 := by norm_num
    rw [← h8] at h5
    exact (pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (8:ℕ) ≠ 0)).1 h5
  have hpi3 := Real.pi_gt_d2
  have e : π * |w.im| / 2 = π * (|w.im| / 2) := by ring
  rw [e]
  calc π ^ (-(-w / 2)).re * ‖(Complex.Gamma (w / 2))⁻¹‖
      ≤ 0.48⁻¹ * (24 / π * Real.exp (π * (|w.im| / 2))) :=
        mul_le_mul hpi hG (norm_nonneg _) (by norm_num)
    _ ≤ 16 * Real.exp (π * (|w.im| / 2)) := by
        have hE := Real.exp_pos (π * (|w.im| / 2))
        have : 0.48⁻¹ * (24 / π) ≤ 16 := by
          rw [show (0.48⁻¹ : ℝ) * (24 / π) = 50 / π by norm_num; ring, div_le_iff₀ Real.pi_pos]
          linarith
        nlinarith

/-! ## The bound -/

theorem norm_rootNumber {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖DirichletCharacter.rootNumber χ‖ = 1 := by
  have hN : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ = √N := by
    rw [← TernaryGoldbach.norm_sq_gaussSum_of_isPrimitive hχ, Real.sqrt_sq (norm_nonneg _)]
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, hg, norm_pow, Complex.norm_I, one_pow,
    div_one, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))]
  have : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  rw [this, ← Real.sqrt_eq_rpow, div_self (Real.sqrt_pos.2 hN).ne']

/-- **Growth on the left**: for `χ` primitive, `χ ≠ 1`, `−8 ≤ ℜz ≤ 1/4`:
`|L(z, χ)| ≤ 512 q⁹ (q + 1)(|ℑz| + 9) e^{π|ℑz|/2}`. -/
theorem norm_LFunction_left {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {z : ℂ} (h1 : -8 ≤ z.re) (h2 : z.re ≤ 1 / 4) :
    ‖χ.LFunction z‖ ≤ 512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|z.im| + 9) *
      Real.exp (π * |z.im| / 2) := by
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
  have hGs : ‖DirichletCharacter.gammaFactor χ⁻¹ s‖ ≤ 24 := by
    rcases χ⁻¹.even_or_odd with he | ho
    · rw [he.gammaFactor_def]; exact norm_Gammaℝ_le hσ1 (by linarith)
    · rw [ho.gammaFactor_def]; exact norm_Gammaℝ_le (by simp; linarith) (by simp; linarith)
  have hΛ : DirichletCharacter.completedLFunction χ⁻¹ s =
      DirichletCharacter.gammaFactor χ⁻¹ s * χ⁻¹.LFunction s := by
    have hGs0 : DirichletCharacter.gammaFactor χ⁻¹ s ≠ 0 := by
      rcases χ⁻¹.even_or_odd with he | ho
      · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by linarith)
      · rw [ho.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inr hN)]
    field_simp
  have hG1 : ‖(DirichletCharacter.gammaFactor χ (1 - s))⁻¹‖ ≤ 16 * Real.exp (π * |z.im| / 2) := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def, ← hz]; exact norm_inv_Gammaℝ_le h1 (by linarith)
    · rw [ho.gammaFactor_def, ← hz]
      have := norm_inv_Gammaℝ_le (w := z + 1) (by simp; linarith) (by simp; linarith)
      simpa using this
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
  have hLs : ‖χ⁻¹.LFunction s‖ ≤ ((N : ℝ) + 1) * (|z.im| + 9) / (3 / 4) := by
    refine (norm_LFunction_le hχi (by linarith)).trans ?_
    have hsn : ‖s‖ ≤ |z.im| + 9 := by
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [hsim, abs_neg, abs_of_pos (by linarith : (0:ℝ) < s.re)]; linarith
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsn (by positivity)) (by norm_num) hσ1
  calc (N : ℝ) ^ (s - 1 / 2).re * (‖DirichletCharacter.gammaFactor χ⁻¹ s‖ * ‖χ⁻¹.LFunction s‖) *
        ‖(DirichletCharacter.gammaFactor χ (1 - s))⁻¹‖
      ≤ (N : ℝ) ^ 9 * (24 * (((N : ℝ) + 1) * (|z.im| + 9) / (3 / 4))) *
          (16 * Real.exp (π * |z.im| / 2)) := by
        gcongr
    _ = 512 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|z.im| + 9) * Real.exp (π * |z.im| / 2) := by ring

end TernaryGoldbach.Explicit
