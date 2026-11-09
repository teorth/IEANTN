import TernaryGoldbach.Explicit.ExplicitFormula
import TernaryGoldbach.Prelim.PlancherelReal

/-!
# Mellin–Plancherel on `ℜs = 1/2` for `G_δ`

`∫ |G_δ(1/2 + it)|² dt = 2π ∫₀^∞ |η(u)|² du` (`η(u) = u² e^{−u²/2}`): `mellin_eq_fourier` writes
`G_δ(1/2 + it) = 𝓕F(t/2π)` with `F(u) = e^{−u/2} fδ(e^{−u})`, and Plancherel (`PlancherelReal`).
-/

open Complex MeasureTheory Set Filter FourierTransform
open scoped Real

namespace TernaryGoldbach.Explicit

/-- `F_δ(u) = e^{−u/2} fδ(e^{−u})`. -/
noncomputable def Fhalf (δ u : ℝ) : ℂ := Real.exp (-(1 / 2) * u) • fδ δ (Real.exp (-u))

theorem norm_Fhalf (δ u : ℝ) :
    ‖Fhalf δ u‖ = Real.exp (-(5 / 2) * u) * Real.exp (-(Real.exp (-u)) ^ 2 / 2) := by
  rw [Fhalf, norm_smul, norm_fδ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have e2 : Real.exp (-u) ^ 2 = Real.exp (-(2 * u)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [e2, ← mul_assoc]
  congr 1
  rw [← Real.exp_add]; congr 1; ring

theorem exp_three_halves_le : Real.exp (3 / 2) ≤ 6 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2)]
  have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [Real.exp_pos (1 / 2)]

theorem norm_Fhalf_le (δ u : ℝ) : ‖Fhalf δ u‖ ≤ 6 * Real.exp (-|u|) := by
  rw [norm_Fhalf]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have h1 : Real.exp (-(5 / 2) * u) ≤ Real.exp (-u) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-(Real.exp (-u)) ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := sq_nonneg (Real.exp (-u)); linarith
    calc Real.exp (-(5 / 2) * u) * Real.exp (-(Real.exp (-u)) ^ 2 / 2) ≤ Real.exp (-u) * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ 6 * Real.exp (-u) := by linarith [Real.exp_pos (-u)]
  · rw [abs_of_nonpos hu]
    set a := -u with ha
    have ha0 : 0 ≤ a := by linarith
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * a by linarith)
    have hsq : Real.exp (-u) ^ 2 = Real.exp (2 * a) := by
      rw [← Real.exp_nat_mul]; congr 1
    rw [hsq, ← Real.exp_add]
    have hle' : (5 / 2) * a - Real.exp (2 * a) / 2 ≤ 3 / 2 - a := by nlinarith [sq_nonneg (a - 5 / 4)]
    have hle : -(5 / 2) * u + -(Real.exp (2 * a)) / 2 ≤ 3 / 2 + -a := by
      have hu' : u = -a := by rw [ha]; ring
      rw [hu']; linarith
    calc Real.exp (-(5 / 2) * u + -(Real.exp (2 * a)) / 2) ≤ Real.exp (3 / 2 + -a) :=
          Real.exp_le_exp.2 hle
      _ = Real.exp (3 / 2) * Real.exp (-a) := Real.exp_add _ _
      _ ≤ 6 * Real.exp (-a) := by gcongr; exact exp_three_halves_le

theorem continuous_Fhalf (δ : ℝ) : Continuous (Fhalf δ) := by
  unfold Fhalf; exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-(1 / 2) * u)).smul
    ((continuous_fδ δ).comp (by fun_prop))

theorem integrable_Fhalf (δ : ℝ) : Integrable (Fhalf δ) :=
  ((integrable_exp_neg_abs (c := 1) one_pos).const_mul 6).mono'
    (continuous_Fhalf δ).aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa using norm_Fhalf_le δ u)

theorem memLp_Fhalf (δ : ℝ) : MemLp (Fhalf δ) 2 := by
  refine (memLp_two_iff_integrable_sq_norm (continuous_Fhalf δ).aestronglyMeasurable).2 ?_
  refine ((integrable_exp_neg_abs (c := 2) two_pos).const_mul 36).mono'
    ((continuous_Fhalf δ).norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_Fhalf_le δ u
  have h0 := norm_nonneg (Fhalf δ u)
  have : (6 * Real.exp (-|u|)) ^ 2 = 36 * Real.exp (-(2 * |u|)) := by
    rw [mul_pow, ← Real.exp_nat_mul]; norm_num
  nlinarith [pow_le_pow_left₀ h0 h 2]

theorem G_half_eq_fourier (δ t : ℝ) :
    Gr (((1 / 2 : ℝ) : ℂ) + t * I) δ 0 = 𝓕 (Fhalf δ) (t / (2 * π)) := by
  rw [← mellin_fδ, mellin_eq_fourier]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add]
  congr 1

/-- **Mellin–Plancherel**: `∫ |G_δ(1/2 + it)|² dt = 2π ∫₀^∞ (u² e^{−u²/2})² du`. -/
theorem integral_norm_sq_G_half (δ : ℝ) :
    ∫ t : ℝ, ‖Gr (((1 / 2 : ℝ) : ℂ) + t * I) δ 0‖ ^ 2 =
      2 * π * ∫ u in Ioi (0:ℝ), (u ^ 2 * Real.exp (-u ^ 2 / 2)) ^ 2 := by
  simp_rw [G_half_eq_fourier]
  have h1 := Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (Fhalf δ) ξ‖ ^ 2) (2 * π)
  rw [h1, abs_of_pos (by positivity), smul_eq_mul,
    TernaryGoldbach.integral_norm_sq_fourier (integrable_Fhalf δ) (memLp_Fhalf δ)]
  congr 1
  -- `∫ e^{−u} |fδ(e^{−u})|² du = ∫₀^∞ |fδ|²` via `mellin_eq_fourier` at `s = 1`
  set g : ℝ → ℂ := fun v => (((v ^ 2 * Real.exp (-v ^ 2 / 2)) ^ 2 : ℝ) : ℂ) with hg
  have hm := mellin_eq_fourier g (s := (1 : ℂ))
  simp only [Complex.one_re, Complex.one_im, zero_div] at hm
  rw [Real.fourier_eq] at hm
  simp only [inner_zero_right, neg_zero, Real.fourierChar_apply, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, Circle.smul_def] at hm
  simp only [one_smul] at hm
  rw [mellin] at hm
  have hL : ∫ t in Ioi (0:ℝ), (t : ℂ) ^ ((1:ℂ) - 1) • g t =
      ((∫ u in Ioi (0:ℝ), (u ^ 2 * Real.exp (-u ^ 2 / 2)) ^ 2 : ℝ) : ℂ) := by
    simp only [sub_self, Complex.cpow_zero, one_smul, hg]; exact integral_ofReal
  have hpt : ∀ v : ℝ, Real.exp (-1 * v) • g (Real.exp (-v)) = ((‖Fhalf δ v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [Complex.real_smul, hg, ← Complex.ofReal_mul]
    congr 1
    rw [norm_Fhalf]
    have h5 : Real.exp (-(5 / 2) * v) ^ 2 = Real.exp (-v) ^ 5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h1 : Real.exp (-1 * v) = Real.exp (-v) := by ring_nf
    rw [h1, mul_pow (Real.exp (-(5 / 2) * v)), h5]
    ring
  have hR : ∫ v, Real.exp (-1 * v) • g (Real.exp (-v)) = ((∫ x, ‖Fhalf δ x‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]; exact integral_ofReal
  rw [hL, hR] at hm
  exact_mod_cast hm.symm

/-! ## Changes of variable, and Plancherel for the derivative -/

/-- `∫ e^{−u} g(e^{−u}) du = ∫₀^∞ g` (`mellin_eq_fourier` at `s = 1`). -/
theorem integral_exp_neg_comp (g : ℝ → ℝ) :
    ∫ u : ℝ, Real.exp (-u) * g (Real.exp (-u)) = ∫ v in Ioi (0:ℝ), g v := by
  have hm := mellin_eq_fourier (fun v => (g v : ℂ)) (s := (1 : ℂ))
  simp only [Complex.one_re, Complex.one_im, zero_div] at hm
  rw [Real.fourier_eq] at hm
  simp only [inner_zero_right, neg_zero, Real.fourierChar_apply, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, Circle.smul_def] at hm
  simp only [one_smul] at hm
  rw [mellin] at hm
  have hL : ∫ t in Ioi (0:ℝ), (t : ℂ) ^ ((1:ℂ) - 1) • ((g t : ℝ) : ℂ) = ((∫ v in Ioi (0:ℝ), g v : ℝ) : ℂ) := by
    simp only [sub_self, Complex.cpow_zero, one_smul]; exact integral_ofReal
  have hR : ∫ v : ℝ, Real.exp (-1 * v) • ((g (Real.exp (-v)) : ℝ) : ℂ) =
      ((∫ u : ℝ, Real.exp (-u) * g (Real.exp (-u)) : ℝ) : ℂ) := by
    have e : ∀ v : ℝ, Real.exp (-1 * v) • ((g (Real.exp (-v)) : ℝ) : ℂ) =
        ((Real.exp (-v) * g (Real.exp (-v)) : ℝ) : ℂ) := by
      intro v; rw [Complex.real_smul, ← Complex.ofReal_mul, neg_one_mul]
    simp_rw [e]; exact integral_ofReal
  rw [hL, hR] at hm
  exact_mod_cast hm.symm

/-- `η(v)² = (v² e^{−v²/2})²`. -/
noncomputable def etaSq (v : ℝ) : ℝ := (v ^ 2 * Real.exp (-v ^ 2 / 2)) ^ 2

theorem norm_Fhalf_sq (δ u : ℝ) : ‖Fhalf δ u‖ ^ 2 = Real.exp (-u) * etaSq (Real.exp (-u)) := by
  rw [norm_Fhalf, etaSq]
  have h5 : Real.exp (-(5 / 2) * u) ^ 2 = Real.exp (-u) ^ 5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow (Real.exp (-(5 / 2) * u)), h5]
  ring

theorem integral_norm_sq_Fhalf (δ : ℝ) : ∫ u, ‖Fhalf δ u‖ ^ 2 = ∫ v in Ioi (0:ℝ), etaSq v := by
  simp_rw [norm_Fhalf_sq]; exact integral_exp_neg_comp etaSq

theorem integral_sq_mul_norm_sq_Fhalf (δ : ℝ) :
    ∫ u, u ^ 2 * ‖Fhalf δ u‖ ^ 2 = ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * etaSq v := by
  rw [← integral_exp_neg_comp (fun v => Real.log v ^ 2 * etaSq v)]
  congr 1; ext u
  rw [norm_Fhalf_sq, Real.log_exp]; ring

/-- Continuous functions with `‖g x‖ ≤ C e^{−c|x|}` are in `L¹ ∩ L²`. -/
theorem integrable_memLp_of_exp {g : ℝ → ℂ} (hg : Continuous g) {C c : ℝ} (hc : 0 < c)
    (hb : ∀ x, ‖g x‖ ≤ C * Real.exp (-(c * |x|))) : Integrable g ∧ MemLp g 2 := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg (g 0)).trans (hb 0); simp at this; exact this
  refine ⟨((integrable_exp_neg_abs hc).const_mul C).mono' hg.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hb x), ?_⟩
  refine (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 ?_
  refine ((integrable_exp_neg_abs (c := 2 * c) (by linarith)).const_mul (C ^ 2)).mono'
    (hg.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := hb x
  have h0 := norm_nonneg (g x)
  have : (C * Real.exp (-(c * |x|))) ^ 2 = C ^ 2 * Real.exp (-(2 * c * |x|)) := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  nlinarith [pow_le_pow_left₀ h0 h 2]

theorem norm_smul_Fhalf_le (δ x : ℝ) : ‖x • Fhalf δ x‖ ≤ 12 * Real.exp (-((1 / 2) * |x|)) := by
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := norm_Fhalf_le δ x
  have h2 : |x| ≤ 2 * Real.exp ((1 / 2) * |x|) := by
    have := Real.add_one_le_exp ((1 / 2) * |x|); linarith
  have h3 : Real.exp ((1 / 2) * |x|) * Real.exp (-|x|) = Real.exp (-((1 / 2) * |x|)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |x| * ‖Fhalf δ x‖ ≤ (2 * Real.exp ((1 / 2) * |x|)) * (6 * Real.exp (-|x|)) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = 12 * (Real.exp ((1 / 2) * |x|) * Real.exp (-|x|)) := by ring
    _ = _ := by rw [h3]

theorem integrable_smul_Fhalf (δ : ℝ) : Integrable fun x : ℝ => x • Fhalf δ x :=
  (integrable_memLp_of_exp (continuous_id.smul (continuous_Fhalf δ)) (by norm_num)
    (norm_smul_Fhalf_le δ)).1

/-- `f(t) = G_δ(1/2 + it)`. -/
noncomputable def fline (δ t : ℝ) : ℂ := Gr (((1 / 2 : ℝ) : ℂ) + t * I) δ 0

/-- The integrand of `f'`. -/
noncomputable def FhalfD (δ x : ℝ) : ℂ := (-2 * π * I * x) • Fhalf δ x

/-- `f'(t)`. -/
noncomputable def flineD (δ t : ℝ) : ℂ := (1 / (2 * π) : ℝ) • 𝓕 (FhalfD δ) (t / (2 * π))

theorem norm_FhalfD_le (δ x : ℝ) : ‖FhalfD δ x‖ ≤ 2 * π * 12 * Real.exp (-((1 / 2) * |x|)) := by
  have e : FhalfD δ x = (-2 * π * I) * (x • Fhalf δ x) := by
    rw [FhalfD, smul_eq_mul, Complex.real_smul]; ring
  rw [e, norm_mul]
  have : ‖-2 * π * I‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [this, mul_assoc (2 * π)]
  exact mul_le_mul_of_nonneg_left (norm_smul_Fhalf_le δ x) (by positivity)

theorem continuous_FhalfD (δ : ℝ) : Continuous (FhalfD δ) := by
  have := continuous_Fhalf δ
  unfold FhalfD
  fun_prop

theorem integrable_memLp_FhalfD (δ : ℝ) : Integrable (FhalfD δ) ∧ MemLp (FhalfD δ) 2 :=
  integrable_memLp_of_exp (continuous_FhalfD δ) (by norm_num) (norm_FhalfD_le δ)

theorem fline_eq (δ t : ℝ) : fline δ t = 𝓕 (Fhalf δ) (t / (2 * π)) := G_half_eq_fourier δ t

theorem hasDerivAt_fline (δ t : ℝ) : HasDerivAt (fline δ) (flineD δ t) t := by
  have h := Real.hasDerivAt_fourier (integrable_Fhalf δ) (integrable_smul_Fhalf δ) (t / (2 * π))
  have h2 : HasDerivAt (fun t : ℝ => t / (2 * π)) (1 / (2 * π)) t := by
    simpa using (hasDerivAt_id t).div_const (2 * π)
  have h3 := h.scomp t h2
  have e : fline δ = 𝓕 (Fhalf δ) ∘ fun t : ℝ => t / (2 * π) := funext fun t => fline_eq δ t
  rw [e]
  exact h3

theorem continuous_fline (δ : ℝ) : Continuous (fline δ) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_fline δ t).continuousAt

theorem continuous_flineD (δ : ℝ) : Continuous (flineD δ) := by
  have hc : Continuous (𝓕 (FhalfD δ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      (integrable_memLp_FhalfD δ).1
  have h2 : Continuous fun t : ℝ => t / (2 * π) := by fun_prop
  unfold flineD
  exact (hc.comp h2).const_smul (1 / (2 * π) : ℝ)

theorem integral_norm_sq_fline (δ : ℝ) :
    ∫ t, ‖fline δ t‖ ^ 2 = 2 * π * ∫ v in Ioi (0:ℝ), etaSq v := by
  have := integral_norm_sq_G_half δ
  simp only [fline]
  rw [this]; rfl

theorem integral_norm_sq_flineD (δ : ℝ) :
    ∫ t, ‖flineD δ t‖ ^ 2 = 2 * π * ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * etaSq v := by
  have hpi : 0 < 2 * π := by positivity
  have e1 : ∀ t, ‖flineD δ t‖ ^ 2 = (1 / (2 * π)) ^ 2 * ‖𝓕 (FhalfD δ) (t / (2 * π))‖ ^ 2 := by
    intro t
    rw [flineD, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [e1]
  rw [integral_const_mul]
  have h1 := Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (FhalfD δ) ξ‖ ^ 2) (2 * π)
  rw [h1, abs_of_pos hpi, smul_eq_mul, TernaryGoldbach.integral_norm_sq_fourier
    (integrable_memLp_FhalfD δ).1 (integrable_memLp_FhalfD δ).2]
  have e2 : ∀ x, ‖FhalfD δ x‖ ^ 2 = (2 * π) ^ 2 * (x ^ 2 * ‖Fhalf δ x‖ ^ 2) := by
    intro x
    have e : FhalfD δ x = (-2 * π * I) * (x • Fhalf δ x) := by
      rw [FhalfD, smul_eq_mul, Complex.real_smul]; ring
    rw [e, norm_mul, norm_smul, Real.norm_eq_abs]
    have : ‖-2 * π * I‖ = 2 * π := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [this, mul_pow, mul_pow (|x|), sq_abs]
  simp_rw [e2]
  rw [integral_const_mul, integral_sq_mul_norm_sq_Fhalf]
  field_simp

/-! ## The two constants -/

theorem integral_rpow_exp_sq {q : ℝ} (hq : -1 < q) :
    ∫ v in Ioi (0:ℝ), v ^ q * Real.exp (-v ^ (2:ℝ)) = (1 / 2) * Real.Gamma ((q + 1) / 2) :=
  integral_rpow_mul_exp_neg_rpow (by norm_num) hq

theorem Gamma_five_halves : Real.Gamma (5 / 2) = 3 / 4 * √π := by
  have h1 : Real.Gamma (3 / 2) = 1 / 2 * √π := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), h1]; ring

theorem etaSq_eq {v : ℝ} (_hv : 0 < v) : etaSq v = v ^ (4:ℝ) * Real.exp (-v ^ (2:ℝ)) := by
  have h1 : (v ^ 2) ^ 2 = v ^ 4 := by ring
  have h2 : Real.exp (-v ^ 2 / 2) ^ 2 = Real.exp (-v ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [etaSq, mul_pow, h1, h2, Real.rpow_two, show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- `∫₀^∞ η² = 3√π/8`. -/
theorem integral_etaSq : ∫ v in Ioi (0:ℝ), etaSq v = 3 * √π / 8 := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => etaSq_eq hv,
    integral_rpow_exp_sq (by norm_num)]
  norm_num [Gamma_five_halves]; ring

theorem log_sq_le (v : ℝ) (hv : 0 < v) : Real.log v ^ 2 ≤ v + v⁻¹ - 2 := by
  set t := Real.log v with ht
  have hv' : v = Real.exp t := (Real.exp_log hv).symm
  have hvi : v⁻¹ = Real.exp (-t) := by rw [hv', Real.exp_neg]
  have hs : Real.exp t + Real.exp (-t) - 2 = 4 * Real.sinh (t / 2) ^ 2 := by
    rw [Real.sinh_eq]
    have h1 : Real.exp t = Real.exp (t / 2) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; ring
    have h2 : Real.exp (-t) = Real.exp (-(t / 2)) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
    rw [h1, h2]; nlinarith [h3]
  have hsq : (t / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 := by
    rcases le_total 0 t with h | h
    · have := Real.self_le_sinh_iff.2 (by linarith : 0 ≤ t / 2)
      exact pow_le_pow_left₀ (by linarith) this 2
    · have := Real.sinh_le_self_iff.2 (by linarith : t / 2 ≤ 0)
      nlinarith
  rw [hvi]; nth_rewrite 1 [hv']
  nlinarith

/-- `∫₀^∞ (log v)² η(v)² dv ≤ 3/2 − 3√π/4`. -/
theorem integral_log_sq_etaSq_le :
    ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * etaSq v ≤ 3 / 2 - 3 * √π / 4 := by
  have i5 := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := 5) (by norm_num) (by norm_num)
  have i3 := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := 3) (by norm_num) (by norm_num)
  have i4 := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := 4) (by norm_num) (by norm_num)
  set R : ℝ → ℝ := fun v => v ^ (5:ℝ) * Real.exp (-v ^ (2:ℝ)) + v ^ (3:ℝ) * Real.exp (-v ^ (2:ℝ)) -
    2 * (v ^ (4:ℝ) * Real.exp (-v ^ (2:ℝ))) with hR
  have iR : IntegrableOn R (Ioi 0) := (i5.add i3).sub (i4.const_mul 2)
  have hpt : ∀ v ∈ Ioi (0:ℝ), Real.log v ^ 2 * etaSq v ≤ R v := by
    intro v (hv : 0 < v)
    rw [etaSq_eq hv]
    have h := log_sq_le v hv
    have e : R v = (v + v⁻¹ - 2) * (v ^ (4:ℝ) * Real.exp (-v ^ (2:ℝ))) := by
      simp only [hR]
      have h5 : v ^ (5:ℝ) = v * v ^ (4:ℝ) := by
        rw [show (5:ℝ) = 1 + 4 by norm_num, Real.rpow_add hv, Real.rpow_one]
      have h3 : v ^ (3:ℝ) = v⁻¹ * v ^ (4:ℝ) := by
        rw [show (4:ℝ) = 1 + 3 by norm_num, Real.rpow_add hv, Real.rpow_one, ← mul_assoc,
          inv_mul_cancel₀ hv.ne', one_mul]
      rw [h5, h3]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have iL : IntegrableOn (fun v => Real.log v ^ 2 * etaSq v) (Ioi 0) := by
    refine iR.mono' (by unfold etaSq; fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold etaSq; positivity)]
    exact hpt v hv
  refine (setIntegral_mono_on iL iR measurableSet_Ioi hpt).trans (le_of_eq ?_)
  have hs : ∫ v in Ioi (0:ℝ), R v = (∫ v in Ioi (0:ℝ), v ^ (5:ℝ) * Real.exp (-v ^ (2:ℝ))) +
      (∫ v in Ioi (0:ℝ), v ^ (3:ℝ) * Real.exp (-v ^ (2:ℝ))) -
        2 * ∫ v in Ioi (0:ℝ), v ^ (4:ℝ) * Real.exp (-v ^ (2:ℝ)) := by
    have j1 : IntegrableOn (fun v : ℝ => v ^ (5:ℝ) * Real.exp (-v ^ (2:ℝ)) +
        v ^ (3:ℝ) * Real.exp (-v ^ (2:ℝ))) (Ioi 0) := i5.add i3
    have j2 : IntegrableOn (fun v : ℝ => 2 * (v ^ (4:ℝ) * Real.exp (-v ^ (2:ℝ)))) (Ioi 0) :=
      i4.const_mul 2
    rw [← integral_add i5 i3, ← integral_const_mul, ← integral_sub j1 j2]
  rw [hs, integral_rpow_exp_sq (by norm_num), integral_rpow_exp_sq (by norm_num),
    integral_rpow_exp_sq (by norm_num)]
  have g3 : Real.Gamma 3 = 2 := by
    rw [show (3:ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]; norm_num
  rw [show ((5:ℝ) + 1) / 2 = 3 by norm_num, show ((3:ℝ) + 1) / 2 = 2 by norm_num,
    show ((4:ℝ) + 1) / 2 = 5 / 2 by norm_num, g3, Real.Gamma_two, Gamma_five_halves]
  ring

theorem sqrt_pi_bounds : 1.77245 ≤ √π ∧ √π ≤ 1.77246 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) Real.pi_pos.le]; have := Real.pi_gt_d6; nlinarith
  · rw [Real.sqrt_le_left (by norm_num)]; have := Real.pi_lt_d6; nlinarith

end TernaryGoldbach.Explicit
