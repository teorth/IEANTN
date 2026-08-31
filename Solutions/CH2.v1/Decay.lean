/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Approximants
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Fourier decay of the extremal approximants, and the exact `L¹` errors

Split out of `Approximants.lean` because two of these are NOT ports.

`PrimeNumberTheoremAnd` proves `varphi_fourier_decay` and `varphi_hat_integrable` from
`Wiener.prelim_decay_3` and `Wiener.decay_alt`, and `prelim_decay_3` is one of the two `sorry`s in
that file: the Fourier transform of a function whose derivative has bounded variation decays like
`|u|⁻²`. A proper, upstreamable treatment of Riemann-Stieltjes integration by parts is worth having
and is deliberately out of scope here.

It is also unnecessary. The closed form `Approximants` already proves sorry-free --
`fourier_formula_pos` and `fourier_formula_neg` -- yields the same bound directly, because `B ε` is
globally `1`-Lipschitz along the reals and so the integrand `B ε (ν ∓ t) - B ε ν` vanishes
LINEARLY at `t = 0`. Then `∫₀^∞ t e^{-ct} dt = c⁻²` supplies the second power.

The rest of this file -- `Inu_integral`, `Inu_integrable`, `varphi_fourier_inversion_re` and the
two `L¹` error theorems -- is the upstream material unchanged, moved here only because it sits
between the two replaced theorems and their consumers.
-/

open Real MeasureTheory FourierTransform Chebyshev Asymptotics
open ArithmeticFunction hiding log
open Complex hiding log

namespace CH2

/-! ### The replacement bound -/

/-- `B ε` is `1`-Lipschitz along the reals, in norm. -/
lemma norm_B_sub_ofReal_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (a b : ℝ) :
    ‖B ε (a : ℂ) - B ε (b : ℂ)‖ ≤ |a - b| :=
  (norm_B_sub_ofReal ε a b).le.trans (B_real_lipschitz_of_pm hε)

/-- `∫₀^∞ t e^{-ct} dt = 1/c²`: the second moment that turns linear vanishing of the integrand at
`t = 0` into a second power of decay. -/
lemma integral_Ioi_id_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), t * rexp (-c * t) = 1 / c ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := c) two_pos hc
  rw [Real.Gamma_two, mul_one] at h
  have hcongr : (∫ t in Set.Ioi (0 : ℝ), t * rexp (-c * t))
      = ∫ t in Set.Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * rexp (-(c * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, neg_mul]
  rw [hcongr, h, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow, one_pow]

/-- `t ↦ t e^{-ct}` is integrable on `(0, ∞)` for `c > 0`. -/
lemma integrableOn_id_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ t * rexp (-c * t)) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := c)
    (by norm_num) one_pos hc
  refine h.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- Exponential beats the square: `(1 + u²) e^{-νu} ≤ 54/ν³` for `u ≥ 1`, `ν > 0`.

From `1 + x ≤ eˣ` at `νu/3`, so `e^{νu} = (e^{νu/3})³ ≥ (νu/3)³`. Needed only on the `u > 0`
branch, where `fourier_formula_pos` converges to `𝓕 φ u - e^{-νu}` rather than to `𝓕 φ u`. -/
lemma exp_neg_mul_le_of_one_le {ν u : ℝ} (hν : 0 < ν) (hu : 1 ≤ u) :
    (1 + u ^ 2) * rexp (-(ν * u)) ≤ 54 / ν ^ 3 := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hcube : ν ^ 3 * u ^ 3 / 27 ≤ rexp (ν * u) := by
    have h1 : ν * u / 3 ≤ rexp (ν * u / 3) := by
      have := Real.add_one_le_exp (ν * u / 3); linarith
    have h2 : rexp (ν * u) = rexp (ν * u / 3) ^ 3 := by
      rw [← Real.exp_nat_mul]; ring_nf
    calc ν ^ 3 * u ^ 3 / 27 = (ν * u / 3) ^ 3 := by ring
      _ ≤ rexp (ν * u / 3) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = rexp (ν * u) := h2.symm
  have key : 1 + u ^ 2 ≤ 54 / ν ^ 3 * rexp (ν * u) := by
    have hsq : 1 + u ^ 2 ≤ 2 * u ^ 3 := by nlinarith
    calc 1 + u ^ 2 ≤ 2 * u ^ 3 := hsq
      _ = 54 / ν ^ 3 * (ν ^ 3 * u ^ 3 / 27) := by field_simp; ring
      _ ≤ 54 / ν ^ 3 * rexp (ν * u) := by
          exact mul_le_mul_of_nonneg_left hcube (by positivity)
  calc (1 + u ^ 2) * rexp (-(ν * u))
      ≤ (54 / ν ^ 3 * rexp (ν * u)) * rexp (-(ν * u)) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = 54 / ν ^ 3 := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]


/-- The truncated integral in the closed form is `O(c⁻²)`, uniformly in the truncation point.

`g` is `fun t ↦ ν - t` on the `x > 0` branch and `fun t ↦ ν + t` on the `x < 0` branch; in both,
`|g t - ν| = t` for `t ≥ 0`, which is what the `1`-Lipschitz bound turns into linear vanishing. -/
lemma norm_setIntegral_B_diff_mul_exp_le {ε ν c : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c)
    (g : ℝ → ℝ) (hcont : Continuous g) (hg : ∀ t : ℝ, 0 ≤ t → |g t - ν| ≤ t) (T : ℝ) :
    ‖∫ t in Set.Icc (0 : ℝ) T, ((B ε (g t : ℂ) - B ε (ν : ℂ)) * (rexp (-c * t) : ℂ))‖
      ≤ 1 / c ^ 2 := by
  have hmeas : Continuous fun t : ℝ ↦ (B ε (g t : ℂ) - B ε (ν : ℂ)) * (rexp (-c * t) : ℂ) :=
    (((B.continuous_ofReal ε).comp hcont).sub continuous_const).mul
      (Complex.continuous_ofReal.comp (by fun_prop))
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖(B ε (g t : ℂ) - B ε (ν : ℂ)) * (rexp (-c * t) : ℂ)‖ ≤ t * rexp (-c * t) := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      ((norm_B_sub_ofReal_le hε (g t) ν).trans (hg t ht.1)) (Real.exp_pos _).le
  calc ‖∫ t in Set.Icc (0 : ℝ) T, ((B ε (g t : ℂ) - B ε (ν : ℂ)) * (rexp (-c * t) : ℂ))‖
      ≤ ∫ t in Set.Icc (0 : ℝ) T, ‖(B ε (g t : ℂ) - B ε (ν : ℂ)) * (rexp (-c * t) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Icc (0 : ℝ) T, t * rexp (-c * t) :=
        setIntegral_mono_on (hmeas.norm.integrableOn_Icc)
          (Continuous.integrableOn_Icc (by fun_prop)) measurableSet_Icc hpt
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), t * rexp (-c * t) := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine setIntegral_mono_set (integrableOn_id_mul_exp_neg hc) ?_
          (Filter.Eventually.of_forall fun t ht ↦ ht.1)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (le_of_lt ht) (Real.exp_pos _).le
    _ = 1 / c ^ 2 := integral_Ioi_id_mul_exp_neg hc

/-- **The replacement bound.** `‖𝓕 (ϕ_pm ν ε) u‖ ≤ C/(1 + u²)`, from the closed form rather than
from bounded variation. Both theorems below follow from it. -/
lemma varphi_fourier_bound (ν ε : ℝ) (hν : 0 < ν) (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖𝓕 (ϕ_pm ν ε) u‖ ≤ C / (1 + u ^ 2) := by
  have hlam : ν ≠ 0 := hν.ne'
  -- `𝓕` is the typeclass notation `FourierTransform.fourier`, whose instance on `ℝ → ℂ` is
  -- `VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)`; that is where the uniform bound lives.
  obtain ⟨M, hMnn, htriv⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, ‖𝓕 (ϕ_pm ν ε) u‖ ≤ M :=
    ⟨∫ t : ℝ, ‖ϕ_pm ν ε t‖, integral_nonneg fun _ ↦ norm_nonneg _,
      fun u ↦ VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _⟩
  refine ⟨2 * M + 2 / π ^ 2 + 54 / ν ^ 3, by positivity, fun u ↦ ?_⟩
  have hπ : (0 : ℝ) < π ^ 2 := by positivity
  have hden : (0 : ℝ) < 1 + u ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  rcases le_or_gt |u| 1 with hsmall | hbig
  · -- `|u| ≤ 1`: the trivial bound suffices, since `1 + u² ≤ 2`.
    have h2 : 1 + u ^ 2 ≤ 2 := by nlinarith [sq_abs u, abs_nonneg u]
    have := htriv u
    nlinarith [norm_nonneg (𝓕 (ϕ_pm ν ε) u), div_nonneg (by norm_num : (0:ℝ) ≤ 2) hπ.le,
      div_nonneg (by norm_num : (0:ℝ) ≤ 54) (pow_pos hν 3).le]
  · -- `|u| > 1`: the closed form gives `|u|⁻²`.
    have hu2 : (1 : ℝ) < u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
    have hu2pos : (0 : ℝ) < u ^ 2 := by linarith
    have hfrac : (1 + u ^ 2) * (1 / π ^ 2 * (1 / u ^ 2)) ≤ 2 / π ^ 2 := by
      have h1 : (1 + u ^ 2) / u ^ 2 ≤ 2 := by rw [div_le_iff₀ hu2pos]; linarith
      have h2 : (1 + u ^ 2) * (1 / π ^ 2 * (1 / u ^ 2)) = ((1 + u ^ 2) / u ^ 2) / π ^ 2 := by
        field_simp
      rw [h2]
      gcongr
    rcases lt_abs.mp hbig with hpos | hneg
    · -- `u > 1`
      have hkey : ‖𝓕 (ϕ_pm ν ε) u - Complex.exp (-(ν : ℂ) * (u : ℂ))‖ ≤ 1 / π ^ 2 * (1 / u ^ 2) := by
        refine le_of_tendsto ((fourier_formula_pos ν ε hν u (by linarith)).norm)
          (Filter.Eventually.of_forall fun T ↦ ?_)
        rw [norm_mul]
        have hsin : ‖(-(Real.sin (π * u) : ℂ) ^ 2 / (π : ℂ) ^ 2)‖ ≤ 1 / π ^ 2 := by
          rw [norm_div, norm_neg, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          gcongr
          nlinarith [Real.neg_one_le_sin (π * u), Real.sin_le_one (π * u),
            abs_nonneg (Real.sin (π * u)), sq_abs (Real.sin (π * u))]
        refine mul_le_mul hsin ?_ (norm_nonneg _) (by positivity)
        simpa only [Complex.ofReal_sub] using
          norm_setIntegral_B_diff_mul_exp_le hε (by linarith : (0:ℝ) < u)
            (fun t ↦ ν - t) (by fun_prop)
              (fun t ht ↦ by rw [show ν - t - ν = -t by ring, abs_neg, abs_of_nonneg ht]) T
      have hexp : ‖Complex.exp (-(ν : ℂ) * (u : ℂ))‖ = rexp (-(ν * u)) := by
        rw [Complex.norm_exp]
        norm_num
      have hsplit : ‖𝓕 (ϕ_pm ν ε) u‖ ≤ 1 / π ^ 2 * (1 / u ^ 2) + rexp (-(ν * u)) := by
        calc ‖𝓕 (ϕ_pm ν ε) u‖
            ≤ ‖𝓕 (ϕ_pm ν ε) u - Complex.exp (-(ν : ℂ) * (u : ℂ))‖
              + ‖Complex.exp (-(ν : ℂ) * (u : ℂ))‖ := by
                have h := norm_add_le (𝓕 (ϕ_pm ν ε) u - Complex.exp (-(ν : ℂ) * (u : ℂ)))
                  (Complex.exp (-(ν : ℂ) * (u : ℂ)))
                rwa [sub_add_cancel] at h
          _ ≤ _ := by rw [hexp]; linarith [hkey]
      calc ‖𝓕 (ϕ_pm ν ε) u‖ * (1 + u ^ 2)
          ≤ (1 / π ^ 2 * (1 / u ^ 2) + rexp (-(ν * u))) * (1 + u ^ 2) :=
            mul_le_mul_of_nonneg_right hsplit hden.le
        _ = (1 + u ^ 2) * (1 / π ^ 2 * (1 / u ^ 2)) + (1 + u ^ 2) * rexp (-(ν * u)) := by ring
        _ ≤ 2 / π ^ 2 + 54 / ν ^ 3 := by
            linarith [hfrac, exp_neg_mul_le_of_one_le hν (le_of_lt hpos)]
        _ ≤ 2 * M + 2 / π ^ 2 + 54 / ν ^ 3 := by linarith
    · -- `u < -1`; here the closed form converges to `𝓕 φ u` itself, with no exponential term.
      have hkey : ‖𝓕 (ϕ_pm ν ε) u‖ ≤ 1 / π ^ 2 * (1 / u ^ 2) := by
        refine le_of_tendsto ((fourier_formula_neg ν ε hν u (by linarith)).norm)
          (Filter.Eventually.of_forall fun T ↦ ?_)
        rw [norm_mul]
        have hsin : ‖((Real.sin (π * u) : ℂ) ^ 2 / (π : ℂ) ^ 2)‖ ≤ 1 / π ^ 2 := by
          rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          gcongr
          nlinarith [Real.neg_one_le_sin (π * u), Real.sin_le_one (π * u),
            abs_nonneg (Real.sin (π * u)), sq_abs (Real.sin (π * u))]
        refine mul_le_mul hsin ?_ (norm_nonneg _) (by positivity)
        have hc : (0 : ℝ) < -u := by linarith
        simpa only [Complex.ofReal_add, neg_neg, neg_sq] using
          norm_setIntegral_B_diff_mul_exp_le hε hc (fun t ↦ ν + t) (by fun_prop)
            (fun t ht ↦ by rw [show ν + t - ν = t by ring, abs_of_nonneg ht]) T
      calc ‖𝓕 (ϕ_pm ν ε) u‖ * (1 + u ^ 2)
          ≤ (1 / π ^ 2 * (1 / u ^ 2)) * (1 + u ^ 2) :=
            mul_le_mul_of_nonneg_right hkey hden.le
        _ = (1 + u ^ 2) * (1 / π ^ 2 * (1 / u ^ 2)) := by ring
        _ ≤ 2 / π ^ 2 := hfrac
        _ ≤ 2 * M + 2 / π ^ 2 + 54 / ν ^ 3 := by
            have : (0:ℝ) ≤ 54 / ν ^ 3 := by positivity
            linarith


theorem varphi_fourier_decay (ν ε : ℝ) (hν : 0 < ν) (hε : ε = 1 ∨ ε = -1) :
    IsBigO Filter.atTop (fun x : ℝ ↦ (𝓕 (ϕ_pm ν ε) x).re) (fun x : ℝ ↦ 1 / x ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := varphi_fourier_bound ν ε hν hε
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have h1 : ‖(𝓕 (ϕ_pm ν ε) x).re‖ ≤ ‖𝓕 (ϕ_pm ν ε) x‖ := Complex.abs_re_le_norm _
  have h3 : C / (1 + x ^ 2) ≤ C / x ^ 2 := by
    gcongr; first | positivity | linarith
  have h4 : C * ‖1 / x ^ 2‖ = C / x ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
  linarith [hC x]

lemma Inu_integral (ν : ℝ) (hν : ν > 0) : ∫ x : ℝ, Inu ν x = 1 / ν := by
  unfold Inu
  have h_indicator : (fun x ↦ if 0 ≤ x then rexp (-ν * x) else 0) =
      Set.indicator (Set.Ici 0) (fun x ↦ rexp (-ν * x)) := by
    ext x; unfold Set.indicator; rfl
  rw [h_indicator, integral_indicator measurableSet_Ici,
      integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_lt_zero.mpr hν) 0]
  simp

private lemma Inu_integrable (ν : ℝ) (hν : ν > 0) : Integrable (Inu ν) := by
  unfold Inu
  rw [show (fun x ↦ if 0 ≤ x then rexp (-ν * x) else 0) =
      Set.indicator (Set.Ici 0) (fun x ↦ rexp (-ν * x)) by ext x; rfl]
  rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi 0 hν

private lemma varphi_hat_integrable (ν ε : ℝ) (hν : 0 < ν) (hε : ε = 1 ∨ ε = -1) :
    Integrable (𝓕 (ϕ_pm ν ε)) := by
  obtain ⟨C, hC0, hC⟩ := varphi_fourier_bound ν ε hν hε
  have hf : Integrable (ϕ_pm ν ε) := varphi_integ ν ε hν.ne'
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hf).aestronglyMeasurable
  · filter_upwards with x
    refine (hC x).trans_eq ?_
    rw [div_eq_mul_inv]

lemma varphi_fourier_inversion_re (ν ε : ℝ) (hlam : ν ≠ 0)
    (hf_hat_int : Integrable (𝓕 (ϕ_pm ν ε))) :
    ∫ x : ℝ, (𝓕 (ϕ_pm ν ε) x).re = (ϕ_pm ν ε 0).re := by
  have h_inv := MeasureTheory.Integrable.fourierInv_fourier_eq (varphi_integ ν ε hlam)
    hf_hat_int (v := 0) (ϕ_continuous ν ε hlam).continuousAt
  erw [integral_re hf_hat_int, show ∫ x, 𝓕 (ϕ_pm ν ε) x = 𝓕⁻ (𝓕 (ϕ_pm ν ε)) 0 by rw [fourierInv_eq]; simp, h_inv]
  rfl


theorem varphi_fourier_minus_error (ν : ℝ) (hν : ν > 0) :
    ∫ x in Set.univ, (Inu ν x - (𝓕 (ϕ_pm ν (-1)) x).re) = 1 / ν - 1 / (Real.exp ν - 1) := by
  let hf_hat_int := varphi_hat_integrable ν (-1) hν (Or.inr rfl)
  have h_phi_zero : (ϕ_pm ν (-1) 0).re = 1 / (rexp ν - 1) := by
    simp only [ϕ_pm, Real.sign_zero, ofReal_zero, zero_mul, add_zero, Phi_circ]
    norm_num [coth, Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh]
    simp only [← ofReal_div, ← ofReal_neg, ← ofReal_ofNat, ← ofReal_sub, ← ofReal_add, ← ofReal_exp, ofReal_re]
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero, (Real.exp_eq_one_iff ν).not.mpr hν.ne']
    rw [pow_two, ← Real.exp_add]; ring_nf
    field_simp [show -1 + rexp ν ≠ 0 by rw [add_comm]; exact sub_ne_zero.mpr ((Real.exp_eq_one_iff ν).not.mpr hν.ne')]
    ring
  simp only [MeasureTheory.setIntegral_univ]
  erw [integral_sub (Inu_integrable ν hν) hf_hat_int.re, Inu_integral ν hν,
    varphi_fourier_inversion_re ν (-1) hν.ne' hf_hat_int, h_phi_zero]

theorem varphi_fourier_plus_error (ν : ℝ) (hν : ν > 0) :
    ∫ x in Set.univ, ((𝓕 (ϕ_pm ν 1) x).re - Inu ν x) = 1 / (1 - Real.exp (-ν)) - 1 / ν := by
  let hf_hat_int := varphi_hat_integrable ν 1 hν (Or.inl rfl)
  have h_phi_zero : (ϕ_pm ν 1 0).re = 1 / (1 - Real.exp (-ν)) := by
    simp only [ϕ_pm, Real.sign_zero, ofReal_zero, zero_mul, add_zero, Phi_circ]
    norm_num [coth, Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh]
    simp only [← ofReal_div, ← ofReal_neg, ← ofReal_ofNat, ← ofReal_sub, ← ofReal_add, ← ofReal_exp, ofReal_re]
    rw [Real.exp_neg]
    have h_sinh_nz : rexp (ν / 2) - rexp (- (ν / 2)) ≠ 0 := by
      refine sub_ne_zero.mpr (Real.exp_lt_exp.mpr ?_).ne'; linarith
    field_simp [Real.exp_ne_zero, h_sinh_nz]
    ring_nf; simp only [pow_two, ← Real.exp_add]
    rw [show ν * (1 / 2) + ν * (1 / 2) = ν by ring]; simp only [Real.exp_neg]
    field_simp [Real.exp_ne_zero, h_sinh_nz,
      show rexp ν - 1 ≠ 0 from sub_ne_zero.mpr ((Real.exp_eq_one_iff ν).not.mpr hν.ne'),
      show -1 + rexp ν ≠ 0 by rw [add_comm]; exact sub_ne_zero.mpr ((Real.exp_eq_one_iff ν).not.mpr hν.ne'),
      show 1 - rexp (-ν) ≠ 0 from sub_ne_zero.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hν)).ne.symm]
    ring
  simp only [MeasureTheory.setIntegral_univ]
  erw [integral_sub hf_hat_int.re (Inu_integrable ν hν), Inu_integral ν hν,
    varphi_fourier_inversion_re ν 1 hν.ne' hf_hat_int, h_phi_zero]

end CH2
