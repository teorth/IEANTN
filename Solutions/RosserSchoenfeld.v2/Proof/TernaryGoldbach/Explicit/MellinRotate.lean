import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Mellin transform of the twisted Gaussian `t² e^{-t²/2} e(δt)`, by rotating the ray

For `s = σ + iτ` with `σ > -2` and `δ ∈ ℝ`,
`G_δ(s) = ∫₀^∞ t^{s+1} e^{-t²/2} e^{2πiδt} dt`
is the Mellin transform of `η(t) e(δt)`, `η(t) = t² e^{-t²/2}` ([H, Ch. 8], `F_δ(s + 2)` there).
Substituting `t = r e^{iθ}` (`|θ| < π/4`) does not change the integral: the `θ`-derivative of the
integrand is `i ∂_r (r · integrand)`, whose integral over `r ∈ (0, ∞)` vanishes. The rotated
integrand has modulus `r^{σ+1} e^{-θτ} e^{-r² cos 2θ/2 - 2πδ r sin θ}`; completing the square and
choosing `θ` gives the bounds of [H, Cor 8.0.2] (`k = 2`) with the same exponents `0.1598` and
`0.1065` and smaller constants.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace TernaryGoldbach.Explicit

/-- The integrand of `G_δ(s)` after the substitution `t = r e^{iθ}`. -/
noncomputable def Jr (s : ℂ) (δ θ r : ℝ) : ℂ :=
  (r : ℂ) ^ (s + 1) * cexp (θ * I * (s + 2)) *
    cexp (-(r : ℂ) ^ 2 * cexp (2 * θ * I) / 2 + 2 * π * I * δ * r * cexp (θ * I))

/-- The `θ`-derivative of `Jr`. -/
noncomputable def Dr (s : ℂ) (δ θ r : ℝ) : ℂ :=
  Jr s δ θ r * (I * ((s + 2) - (r : ℂ) ^ 2 * cexp (2 * θ * I) + 2 * π * I * δ * r * cexp (θ * I)))

/-- `r · Jr`, whose `r`-derivative is `Dr / i`. -/
noncomputable def Pr (s : ℂ) (δ θ r : ℝ) : ℂ :=
  (r : ℂ) ^ (s + 2) * cexp (θ * I * (s + 2)) *
    cexp (-(r : ℂ) ^ 2 * cexp (2 * θ * I) / 2 + 2 * π * I * δ * r * cexp (θ * I))

theorem re_exponent (δ θ r : ℝ) :
    (-(r : ℂ) ^ 2 * cexp (2 * θ * I) / 2 + 2 * π * I * δ * r * cexp (θ * I)).re =
      -r ^ 2 * Real.cos (2 * θ) / 2 - 2 * π * δ * r * Real.sin θ := by
  have h1 : cexp (2 * θ * I) = ((Real.cos (2 * θ) : ℝ) : ℂ) + ((Real.sin (2 * θ) : ℝ) : ℂ) * I := by
    rw [show (2 : ℂ) * θ * I = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h2 : cexp (θ * I) = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e : -(r : ℂ) ^ 2 * cexp (2 * θ * I) / 2 + 2 * π * I * δ * r * cexp (θ * I) =
      ((-r ^ 2 * Real.cos (2 * θ) / 2 - 2 * π * δ * r * Real.sin θ : ℝ) : ℂ) +
        ((-r ^ 2 * Real.sin (2 * θ) / 2 + 2 * π * δ * r * Real.cos θ : ℝ) : ℂ) * I := by
    rw [h1, h2]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [e, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

theorem norm_Jr (s : ℂ) (δ θ : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖Jr s δ θ r‖ = r ^ (s.re + 1) *
      Real.exp (-θ * s.im - r ^ 2 * Real.cos (2 * θ) / 2 - 2 * π * δ * r * Real.sin θ) := by
  rw [Jr, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp,
    Complex.norm_exp, re_exponent]
  have : (↑θ * I * (s + 2)).re = -θ * s.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Complex.add_re, Complex.one_re, mul_assoc, ← Real.exp_add]
  congr 2; ring

theorem norm_Pr (s : ℂ) (δ θ : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖Pr s δ θ r‖ = r ^ (s.re + 2) *
      Real.exp (-θ * s.im - r ^ 2 * Real.cos (2 * θ) / 2 - 2 * π * δ * r * Real.sin θ) := by
  rw [Pr, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp,
    Complex.norm_exp, re_exponent]
  have : (↑θ * I * (s + 2)).re = -θ * s.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Complex.add_re, Complex.re_ofNat, mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- `∂_θ Jr = Dr`. -/
theorem hasDerivAt_Jr_theta (s : ℂ) (δ r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Jr s δ θ r) (Dr s δ θ r) θ := by
  have hθ : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
  have h1 : HasDerivAt (fun θ : ℝ => cexp (θ * I * (s + 2)))
      (cexp (θ * I * (s + 2)) * (I * (s + 2))) θ := by
    have := ((hθ.mul_const I).mul_const (s + 2)).cexp
    convert this using 1; ring
  have h2 : HasDerivAt (fun θ : ℝ => cexp (2 * θ * I)) (cexp (2 * θ * I) * (2 * I)) θ := by
    have := ((hθ.const_mul 2).mul_const I).cexp
    convert this using 1; ring
  have h3 : HasDerivAt (fun θ : ℝ => cexp (θ * I)) (cexp (θ * I) * I) θ := by
    have := (hθ.mul_const I).cexp
    convert this using 1; ring
  have hE : HasDerivAt (fun θ : ℝ => -(r : ℂ) ^ 2 * cexp (2 * θ * I) / 2 +
      2 * π * I * δ * r * cexp (θ * I))
      (-(r : ℂ) ^ 2 * (cexp (2 * θ * I) * (2 * I)) / 2 + 2 * π * I * δ * r * (cexp (θ * I) * I)) θ :=
    ((h2.const_mul (-(r : ℂ) ^ 2)).div_const 2).add (h3.const_mul (2 * π * I * δ * r))
  refine ((h1.const_mul ((r : ℂ) ^ (s + 1))).mul hE.cexp).congr_deriv ?_
  simp only [Dr, Jr]; ring

/-- `∂_r Pr = Dr / i` for `r > 0`. -/
theorem hasDerivAt_Pr_r (s : ℂ) (δ θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => Pr s δ θ r) (-I * Dr s δ θ r) r := by
  have hr' : (r : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.2 hr
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s + 2)) ((s + 2) * (r : ℂ) ^ (s + 2 - 1)) r :=
    ((hasDerivAt_id (r : ℂ)).cpow_const hr').comp_ofReal.congr_deriv (by simp)
  have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
  have hE : HasDerivAt (fun y : ℝ => -(y : ℂ) ^ 2 * cexp (2 * θ * I) / 2 +
      2 * π * I * δ * y * cexp (θ * I))
      (-(2 * (r : ℂ)) * cexp (2 * θ * I) / 2 + 2 * π * I * δ * cexp (θ * I)) r := by
    have h1 := ((hy.pow 2).neg.mul_const (cexp (2 * θ * I))).div_const 2
    have h2 := (hy.const_mul (2 * π * I * δ)).mul_const (cexp (θ * I))
    exact (h1.add h2).congr_deriv (by simp <;> ring)
  refine ((hc.mul_const (cexp (θ * I * (s + 2)))).mul hE.cexp).congr_deriv ?_
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e1 : (r : ℂ) ^ (s + 2 - 1) = (r : ℂ) ^ (s + 1) := by ring_nf
  have e2 : (r : ℂ) ^ (s + 2) = (r : ℂ) ^ (s + 1) * r := by
    rw [show s + 2 = (s + 1) + 1 by ring, Complex.cpow_add _ _ hr0, Complex.cpow_one]
  rw [e1, e2]
  have hII : -I * I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  simp only [Dr]
  rw [show -I * (Jr s δ θ r * (I * ((s + 2) - (r : ℂ) ^ 2 * cexp (2 * θ * I) +
      2 * π * I * δ * r * cexp (θ * I)))) = Jr s δ θ r * ((s + 2) - (r : ℂ) ^ 2 * cexp (2 * θ * I) +
      2 * π * I * δ * r * cexp (θ * I)) * (-I * I) by ring, hII, mul_one]
  simp only [Jr]
  ring

/-! ## Integrability and the vanishing of `∫ ∂_θ` -/

theorem exp_quad_le {a b r : ℝ} (ha : 0 < a) :
    Real.exp (-a * r ^ 2 + b * r) ≤ Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * r ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ (a / 2) * (r - b / a) ^ 2 := by positivity
  have e : (a / 2) * (r - b / a) ^ 2 = a / 2 * r ^ 2 - b * r + b ^ 2 / (2 * a) := by
    field_simp; ring
  nlinarith

theorem integrableOn_rpow_mul_exp_quad {p a b : ℝ} (hp : -1 < p) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r ^ p * Real.exp (-a * r ^ 2 + b * r)) (Ioi 0) := by
  have hi := (integrableOn_rpow_mul_exp_neg_mul_sq (half_pos ha) hp).const_mul
    (Real.exp (b ^ 2 / (2 * a)))
  refine hi.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun r hr => ?_) measurableSet_Ioi
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hr))).mul
      (by fun_prop)).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := Real.rpow_nonneg (le_of_lt hr) p; positivity)]
    have h := exp_quad_le (b := b) (r := r) ha
    have hp0 : 0 ≤ r ^ p := Real.rpow_nonneg (le_of_lt hr) p
    calc r ^ p * Real.exp (-a * r ^ 2 + b * r)
        ≤ r ^ p * (Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * r ^ 2)) :=
          mul_le_mul_of_nonneg_left h hp0
      _ = Real.exp (b ^ 2 / (2 * a)) * (r ^ p * Real.exp (-(a / 2) * r ^ 2)) := by ring

theorem tendsto_rpow_mul_exp_quad {p a b : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => r ^ p * Real.exp (-a * r ^ 2 + b * r)) atTop (𝓝 0) := by
  have h1 := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (half_pos ha) p).trans_tendsto
    (by
      have : Tendsto (fun x : ℝ => -(1 / 2) * x) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by norm_num)
      exact Real.tendsto_exp_atBot.comp this)
  have h2 := h1.const_mul (Real.exp (b ^ 2 / (2 * a)))
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have := Real.rpow_nonneg (le_of_lt hr) p; positivity
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have h := exp_quad_le (b := b) (r := r) ha
    have hp0 : 0 ≤ r ^ p := Real.rpow_nonneg (le_of_lt hr) p
    calc r ^ p * Real.exp (-a * r ^ 2 + b * r)
        ≤ r ^ p * (Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * r ^ 2)) :=
          mul_le_mul_of_nonneg_left h hp0
      _ = Real.exp (b ^ 2 / (2 * a)) * (r ^ p * Real.exp (-(a / 2) * r ^ 2)) := by ring

/-- Uniform bound on the rotated integrand for `|θ| ≤ θ₁`. -/
theorem norm_Jr_le (s : ℂ) (δ : ℝ) {θ θ₁ r : ℝ} (hr : 0 < r) (hθ : |θ| ≤ θ₁) (hθ₁ : θ₁ ≤ π / 2) :
    ‖Jr s δ θ r‖ ≤ Real.exp (θ₁ * |s.im|) *
      (r ^ (s.re + 1) * Real.exp (-(Real.cos (2 * θ₁) / 2) * r ^ 2 + (2 * π * |δ|) * r)) := by
  rw [norm_Jr s δ θ hr]
  have hc : Real.cos (2 * θ₁) ≤ Real.cos (2 * θ) := by
    rw [← Real.cos_abs (2 * θ), abs_mul, abs_two]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
      (by linarith)
  have h1 : -θ * s.im ≤ θ₁ * |s.im| := by
    have := neg_abs_le (θ * s.im); rw [abs_mul] at this
    nlinarith [abs_nonneg s.im, abs_nonneg θ, neg_le_abs (θ * s.im)]
  have h2 : -(2 * π * δ * r * Real.sin θ) ≤ 2 * π * |δ| * r := by
    have hs := Real.abs_sin_le_one θ
    have : |2 * π * δ * r * Real.sin θ| ≤ 2 * π * |δ| * r := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_of_pos hr]
      exact mul_le_of_le_one_right (by positivity) hs
    linarith [neg_abs_le (2 * π * δ * r * Real.sin θ)]
  have h3 : -(r ^ 2 * Real.cos (2 * θ) / 2) ≤ -(Real.cos (2 * θ₁) / 2) * r ^ 2 := by
    nlinarith [sq_nonneg r]
  rw [mul_left_comm, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (Real.rpow_nonneg hr.le _)

theorem continuousOn_Jr (s : ℂ) (δ θ : ℝ) : ContinuousOn (Jr s δ θ) (Ioi 0) := by
  intro r hr
  refine ContinuousAt.continuousWithinAt ?_
  unfold Jr
  have h1 : ContinuousAt (fun r : ℝ => (r : ℂ) ^ (s + 1)) r :=
    Complex.continuousAt_ofReal_cpow_const r (s + 1) (Or.inr (ne_of_gt hr))
  exact (h1.mul continuousAt_const).mul (by fun_prop)

theorem continuousOn_Dr (s : ℂ) (δ θ : ℝ) : ContinuousOn (Dr s δ θ) (Ioi 0) := by
  refine (continuousOn_Jr s δ θ).mul ?_
  exact Continuous.continuousOn (by fun_prop)

theorem integrableOn_Jr (s : ℂ) (δ : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) (hs : -2 < s.re) :
    IntegrableOn (Jr s δ θ) (Ioi 0) := by
  have hc : 0 < Real.cos (2 * |θ|) / 2 := by
    have := Real.cos_pos_of_mem_Ioo (x := 2 * |θ|) ⟨by linarith [abs_nonneg θ, Real.pi_pos],
      by linarith⟩
    positivity
  refine ((integrableOn_rpow_mul_exp_quad (p := s.re + 1) (b := 2 * π * |δ|) (by linarith)
    hc).const_mul (Real.exp (|θ| * |s.im|))).mono' ((continuousOn_Jr s δ θ).aestronglyMeasurable
    measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
  exact norm_Jr_le s δ hr le_rfl (by linarith [Real.pi_pos])

theorem norm_Dr_le (s : ℂ) (δ θ r : ℝ) (hr : 0 < r) :
    ‖Dr s δ θ r‖ ≤ ‖Jr s δ θ r‖ * (‖s + 2‖ + r ^ 2 + 2 * π * |δ| * r) := by
  rw [Dr, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_mul, Complex.norm_I, one_mul]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))) (le_of_eq ?_)
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      show (2 : ℂ) * θ * I = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_I, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos Real.pi_pos]
    norm_num

theorem integrableOn_Dr_bound (s : ℂ) (δ : ℝ) {θ₁ : ℝ} (hθ₁ : θ₁ < π / 4) (hθ₀ : 0 ≤ θ₁)
    (hs : -2 < s.re) :
    IntegrableOn (fun r => Real.exp (θ₁ * |s.im|) *
      (r ^ (s.re + 1) * Real.exp (-(Real.cos (2 * θ₁) / 2) * r ^ 2 + (2 * π * |δ|) * r)) *
        (‖s + 2‖ + r ^ 2 + 2 * π * |δ| * r)) (Ioi 0) := by
  have hc : 0 < Real.cos (2 * θ₁) / 2 := by
    have := Real.cos_pos_of_mem_Ioo (x := 2 * θ₁) ⟨by linarith [Real.pi_pos], by linarith⟩
    positivity
  have i0 := integrableOn_rpow_mul_exp_quad (p := s.re + 1) (b := 2 * π * |δ|) (by linarith) hc
  have i2 := integrableOn_rpow_mul_exp_quad (p := s.re + 3) (b := 2 * π * |δ|) (by linarith) hc
  have i1 := integrableOn_rpow_mul_exp_quad (p := s.re + 2) (b := 2 * π * |δ|) (by linarith) hc
  have i := ((i0.const_mul ‖s + 2‖).add (i2.add (i1.const_mul (2 * π * |δ|)))).const_mul
    (Real.exp (θ₁ * |s.im|))
  refine IntegrableOn.congr_fun (μ := volume) (s := Ioi (0:ℝ)) i (fun r hr => ?_) measurableSet_Ioi
  have hr : (0:ℝ) < r := hr
  have e2 : r ^ (s.re + 3) = r ^ (s.re + 1) * r ^ 2 := by
    rw [show s.re + 3 = (s.re + 1) + 2 by ring, Real.rpow_add hr, Real.rpow_two]
  have e1 : r ^ (s.re + 2) = r ^ (s.re + 1) * r := by
    rw [show s.re + 2 = (s.re + 1) + 1 by ring, Real.rpow_add hr, Real.rpow_one]
  simp only [Pi.add_apply]
  rw [e2, e1]; ring

/-- `∫₀^∞ ∂_θ Jr dr = 0`. -/
theorem integral_Dr_eq_zero (s : ℂ) (δ : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) (hs : -2 < s.re) :
    ∫ r in Ioi (0:ℝ), Dr s δ θ r = 0 := by
  have hc : 0 < Real.cos (2 * |θ|) / 2 := by
    have := Real.cos_pos_of_mem_Ioo (x := 2 * |θ|) ⟨by linarith [abs_nonneg θ, Real.pi_pos],
      by linarith⟩
    positivity
  have hint : IntegrableOn (Dr s δ θ) (Ioi 0) := by
    refine (integrableOn_Dr_bound s δ (θ₁ := |θ|) hθ (abs_nonneg θ) hs).mono'
      ((continuousOn_Dr s δ θ).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
    have hr' : (0:ℝ) < r := hr
    refine (norm_Dr_le s δ θ r hr').trans ?_
    exact mul_le_mul_of_nonneg_right (norm_Jr_le s δ hr' le_rfl (by linarith [Real.pi_pos]))
      (by positivity)
  have hs2 : (0:ℝ) < (s + 2).re := by simp; linarith
  have hcont : ContinuousWithinAt (Pr s δ θ) (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt ?_
    unfold Pr
    exact ((Complex.continuousAt_ofReal_cpow_const 0 (s + 2) (Or.inl hs2)).mul
      continuousAt_const).mul (by fun_prop)
  have hlim : Tendsto (Pr s δ θ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_rpow_mul_exp_quad (p := s.re + 2) (b := 2 * π * |δ|) hc).const_mul
      (Real.exp (|θ| * |s.im|))
    rw [mul_zero] at h
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [norm_Pr s δ θ hr]
    have hJ := norm_Jr_le s δ hr (le_refl |θ|) (by linarith [Real.pi_pos])
    rw [norm_Jr s δ θ hr] at hJ
    have e1 : r ^ (s.re + 2) = r ^ (s.re + 1) * r := by
      rw [show s.re + 2 = (s.re + 1) + 1 by ring, Real.rpow_add hr, Real.rpow_one]
    rw [e1]
    calc r ^ (s.re + 1) * r * Real.exp (-θ * s.im - r ^ 2 * Real.cos (2 * θ) / 2 -
          2 * π * δ * r * Real.sin θ)
        = r * (r ^ (s.re + 1) * Real.exp (-θ * s.im - r ^ 2 * Real.cos (2 * θ) / 2 -
          2 * π * δ * r * Real.sin θ)) := by ring
      _ ≤ r * (Real.exp (|θ| * |s.im|) * (r ^ (s.re + 1) *
          Real.exp (-(Real.cos (2 * |θ|) / 2) * r ^ 2 + 2 * π * |δ| * r))) :=
          mul_le_mul_of_nonneg_left hJ hr.le
      _ = Real.exp (|θ| * |s.im|) * (r ^ (s.re + 1) * r *
          Real.exp (-(Real.cos (2 * |θ|) / 2) * r ^ 2 + 2 * π * |δ| * r)) := by ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun r hr => hasDerivAt_Pr_r s δ θ hr)
    (hint.const_mul (-I)) hlim
  have hP0 : Pr s δ θ 0 = 0 := by
    unfold Pr
    rw [Complex.ofReal_zero, Complex.zero_cpow (by intro h; rw [h] at hs2; simp at hs2)]
    simp
  rw [hP0, sub_zero, integral_const_mul] at h
  have hI : (-I : ℂ) ≠ 0 := by simp
  exact (mul_eq_zero.1 h).resolve_left hI

/-! ## The rotated integral does not depend on `θ` -/

/-- The rotated integral `∫₀^∞ Jr dr`; at `θ = 0` it is `G_δ(s)`. -/
noncomputable def Gr (s : ℂ) (δ θ : ℝ) : ℂ := ∫ r in Ioi (0:ℝ), Jr s δ θ r

theorem hasDerivAt_Gr (s : ℂ) (δ : ℝ) {θ₀ : ℝ} (hθ : |θ₀| < π / 4) (hs : -2 < s.re) :
    HasDerivAt (fun θ => Gr s δ θ) 0 θ₀ := by
  set ε := (π / 4 - |θ₀|) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set θ₁ := |θ₀| + ε with hθ₁def
  have hθ₁ : θ₁ < π / 4 := by rw [hθ₁def, hε]; linarith
  have hθ₁0 : 0 ≤ θ₁ := by rw [hθ₁def]; positivity
  have hball : ∀ θ ∈ Metric.ball θ₀ ε, |θ| ≤ θ₁ := fun θ hθ => by
    rw [Metric.mem_ball, Real.dist_eq] at hθ
    have := abs_sub_abs_le_abs_sub θ θ₀
    rw [hθ₁def]; linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun θ r => Jr s δ θ r) (F' := fun θ r => Dr s δ θ r) (x₀ := θ₀)
    (bound := fun r => Real.exp (θ₁ * |s.im|) * (r ^ (s.re + 1) *
      Real.exp (-(Real.cos (2 * θ₁) / 2) * r ^ 2 + (2 * π * |δ|) * r)) *
        (‖s + 2‖ + r ^ 2 + 2 * π * |δ| * r))
    (Metric.ball_mem_nhds θ₀ hε0)
    (Filter.Eventually.of_forall fun θ =>
      (continuousOn_Jr s δ θ).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_Jr s δ hθ hs)
    ((continuousOn_Dr s δ θ₀).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr θ hθ => by
      have hr' : (0:ℝ) < r := hr
      refine (norm_Dr_le s δ θ r hr').trans ?_
      exact mul_le_mul_of_nonneg_right
        (norm_Jr_le s δ hr' (hball θ hθ) (by linarith [Real.pi_pos])) (by positivity)))
    (integrableOn_Dr_bound s δ hθ₁ hθ₁0 hs)
    (Filter.Eventually.of_forall fun r θ _ => hasDerivAt_Jr_theta s δ r θ)
  have h2 := h.2
  rw [integral_Dr_eq_zero s δ hθ hs] at h2
  exact h2

theorem Gr_eq (s : ℂ) (δ : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) (hs : -2 < s.re) :
    Gr s δ θ = Gr s δ 0 := by
  have hmem : ∀ {t : ℝ}, |t| < π / 4 → t ∈ Ioo (-(π / 4)) (π / 4) := fun {t} h =>
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have h := (convex_Ioo (-(π / 4)) (π / 4)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun θ => Gr s δ θ) (f' := fun _ => (0 : ℂ)) (C := 0)
    (fun t ht => (hasDerivAt_Gr s δ (abs_lt.2 ⟨ht.1, ht.2⟩) hs).hasDerivWithinAt)
    (fun _ _ => by simp) (hmem (by rw [abs_zero]; positivity)) (hmem hθ)
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

/-! ## The bound -/

theorem norm_Gr_le (s : ℂ) (δ : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) (hs : -2 < s.re)
    (hsg : 0 ≤ θ * s.im) :
    ‖Gr s δ 0‖ ≤ Real.exp (-(|θ| * |s.im|)) * ∫ r in Ioi (0:ℝ),
      r ^ (s.re + 1) * Real.exp (-(Real.cos (2 * θ) / 2) * r ^ 2 + (2 * π * |δ| * |Real.sin θ|) * r) := by
  rw [← Gr_eq s δ hθ hs, Gr]
  have hc : 0 < Real.cos (2 * θ) / 2 := by
    have := Real.cos_pos_of_mem_Ioo (x := 2 * θ) ⟨by linarith [neg_abs_le θ, Real.pi_pos],
      by linarith [le_abs_self θ]⟩
    positivity
  have hi := integrableOn_rpow_mul_exp_quad (p := s.re + 1) (b := 2 * π * |δ| * |Real.sin θ|)
    (by linarith) hc
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hi.const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_))
  have hr' : (0:ℝ) < r := hr
  rw [norm_Jr s δ θ hr', mul_left_comm, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hr'.le _)
  have h1 : -θ * s.im = -(|θ| * |s.im|) := by
    rw [← abs_mul, abs_of_nonneg hsg]; ring
  have h2 : -(2 * π * δ * r * Real.sin θ) ≤ 2 * π * |δ| * |Real.sin θ| * r := by
    have : |2 * π * δ * r * Real.sin θ| = 2 * π * |δ| * |Real.sin θ| * r := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_of_pos hr']
      ring
    linarith [neg_abs_le (2 * π * δ * r * Real.sin θ)]
  rw [h1]; nlinarith

/-! ## A Gaussian integral -/

theorem integral_gauss_odd {c : ℝ} : ∫ u : ℝ, u * Real.exp (-(c / 2) * u ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun u : ℝ => u * Real.exp (-(c / 2) * u ^ 2)) volume
  simp only [neg_mul, neg_sq, integral_neg] at h ⊢
  linarith

theorem integral_gauss_sq {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, u ^ 2 * Real.exp (-(c / 2) * u ^ 2) = √π / (c * √(c / 2)) := by
  have hc2 : 0 < c / 2 := half_pos hc
  have h := integral_comp_abs (f := fun y : ℝ => y ^ 2 * Real.exp (-(c / 2) * y ^ 2))
  simp only [sq_abs] at h
  rw [h]
  have hG := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := c / 2) (by norm_num)
    (by norm_num) hc2
  have e1 : ∫ x in Ioi (0:ℝ), x ^ (2:ℝ) * Real.exp (-(c / 2) * x ^ (2:ℝ)) =
      ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(c / 2) * x ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [Real.rpow_two]
  rw [← e1, hG]
  have hΓ : Real.Gamma ((2 + 1) / 2) = √π / 2 := by
    rw [show ((2:ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]; ring
  have hr : (c / 2) ^ (-((2:ℝ) + 1) / 2) = 1 / (c / 2 * √(c / 2)) := by
    rw [show -((2:ℝ) + 1) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hc2.le,
      Real.rpow_add hc2, Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring
  rw [hΓ, hr]
  have : 0 < √(c / 2) := Real.sqrt_pos.2 hc2
  field_simp

/-- `∫₀^∞ r^p e^{-c r²/2 + b r} dr ≤ e^{b²/2c} ((1 + (b/c)²) √(2π/c) + √π/(c√(c/2)))` for
`0 ≤ p ≤ 2`. -/
theorem integral_rpow_exp_quad_le {p c b : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (hc : 0 < c) :
    ∫ r in Ioi (0:ℝ), r ^ p * Real.exp (-(c / 2) * r ^ 2 + b * r) ≤
      Real.exp (b ^ 2 / (2 * c)) * ((1 + (b / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2))) := by
  have hc2 : 0 < c / 2 := half_pos hc
  set r₀ := b / c with hr₀
  -- the comparison function on `ℝ`
  set g : ℝ → ℝ := fun u => (1 + (u + r₀) ^ 2) * Real.exp (-(c / 2) * u ^ 2) with hg
  have i0 : Integrable fun u : ℝ => Real.exp (-(c / 2) * u ^ 2) := integrable_exp_neg_mul_sq hc2
  have i1 : Integrable fun u : ℝ => u * Real.exp (-(c / 2) * u ^ 2) := integrable_mul_exp_neg_mul_sq hc2
  have i2 : Integrable fun u : ℝ => u ^ 2 * Real.exp (-(c / 2) * u ^ 2) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hc2 (s := 2) (by norm_num)
    simpa only [Real.rpow_two] using this
  have hgexp : g = fun u => (1 + r₀ ^ 2) * Real.exp (-(c / 2) * u ^ 2) +
      (2 * r₀) * (u * Real.exp (-(c / 2) * u ^ 2)) + u ^ 2 * Real.exp (-(c / 2) * u ^ 2) := by
    ext u; simp only [hg]; ring
  have ig : Integrable g := by
    rw [hgexp]; exact ((i0.const_mul _).add (i1.const_mul _)).add i2
  have iA : Integrable fun u : ℝ => (1 + r₀ ^ 2) * Real.exp (-(c / 2) * u ^ 2) := i0.const_mul _
  have iB : Integrable fun u : ℝ => (2 * r₀) * (u * Real.exp (-(c / 2) * u ^ 2)) := i1.const_mul _
  have iAB : Integrable fun u : ℝ => (1 + r₀ ^ 2) * Real.exp (-(c / 2) * u ^ 2) +
      (2 * r₀) * (u * Real.exp (-(c / 2) * u ^ 2)) := iA.add iB
  have hgint : ∫ u, g u = (1 + r₀ ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)) := by
    have e : ∫ u, g u = ∫ u, ((1 + r₀ ^ 2) * Real.exp (-(c / 2) * u ^ 2) +
        (2 * r₀) * (u * Real.exp (-(c / 2) * u ^ 2)) + u ^ 2 * Real.exp (-(c / 2) * u ^ 2)) := by
      rw [hgexp]
    rw [e, integral_add iAB i2, integral_add iA iB, integral_const_mul, integral_const_mul,
      integral_gaussian, integral_gauss_odd, integral_gauss_sq hc]
    ring
  -- translate
  have htr : ∫ r, g (r - r₀) = ∫ u, g u := integral_sub_right_eq_self g r₀
  have ig' : Integrable fun r => g (r - r₀) := ig.comp_sub_right r₀
  have hpt : ∀ r ∈ Ioi (0:ℝ), r ^ p * Real.exp (-(c / 2) * r ^ 2 + b * r) ≤
      Real.exp (b ^ 2 / (2 * c)) * g (r - r₀) := fun r hr => by
    have hr' : (0:ℝ) < r := hr
    have hrp : r ^ p ≤ 1 + r ^ 2 := by
      rcases le_total r 1 with h | h
      · have := Real.rpow_le_one hr'.le h hp0; nlinarith [sq_nonneg r]
      · have := Real.rpow_le_rpow_of_exponent_le h hp2
        rw [Real.rpow_two] at this; linarith
    have he : -(c / 2) * r ^ 2 + b * r = b ^ 2 / (2 * c) + -(c / 2) * (r - r₀) ^ 2 := by
      rw [hr₀]; field_simp; ring
    simp only [hg, sub_add_cancel]
    rw [he, Real.exp_add]
    have h0 : 0 ≤ Real.exp (b ^ 2 / (2 * c)) * Real.exp (-(c / 2) * (r - r₀) ^ 2) := by positivity
    calc r ^ p * (Real.exp (b ^ 2 / (2 * c)) * Real.exp (-(c / 2) * (r - r₀) ^ 2))
        ≤ (1 + r ^ 2) * (Real.exp (b ^ 2 / (2 * c)) * Real.exp (-(c / 2) * (r - r₀) ^ 2)) :=
          mul_le_mul_of_nonneg_right hrp h0
      _ = _ := by ring
  have hgnn : ∀ r, 0 ≤ Real.exp (b ^ 2 / (2 * c)) * g (r - r₀) := fun r => by
    simp only [hg]; positivity
  calc ∫ r in Ioi (0:ℝ), r ^ p * Real.exp (-(c / 2) * r ^ 2 + b * r)
      ≤ ∫ r in Ioi (0:ℝ), Real.exp (b ^ 2 / (2 * c)) * g (r - r₀) :=
        setIntegral_mono_on (integrableOn_rpow_mul_exp_quad (by linarith) hc2)
          (ig'.const_mul _).integrableOn
          measurableSet_Ioi hpt
    _ ≤ ∫ r, Real.exp (b ^ 2 / (2 * c)) * g (r - r₀) :=
        setIntegral_le_integral (ig'.const_mul _) (Filter.Eventually.of_forall hgnn)
    _ = _ := by rw [integral_const_mul, htr, hgint]

/-! ## Closed-form bound for a rotation angle `θ ∈ [0, π/4)` -/

theorem norm_Gr_le_closed (s : ℂ) (δ : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < π / 4)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖Gr s δ 0‖ ≤ Real.exp (-(θ * |s.im|)) *
      (Real.exp ((2 * π * |δ| * Real.sin θ) ^ 2 / (2 * Real.cos (2 * θ))) *
        ((1 + (2 * π * |δ| * Real.sin θ / Real.cos (2 * θ)) ^ 2) * √(π / (Real.cos (2 * θ) / 2)) +
          √π / (Real.cos (2 * θ) * √(Real.cos (2 * θ) / 2)))) := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos (2 * θ) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  set θ' := if 0 ≤ s.im then θ else -θ with hθ'
  have habs : |θ'| = θ := by rw [hθ']; split_ifs <;> simp [abs_of_nonneg hθ0]
  have hcos : Real.cos (2 * θ') = Real.cos (2 * θ) := by
    rw [hθ']; split_ifs
    · rfl
    · rw [mul_neg, Real.cos_neg]
  have hsin' : |Real.sin θ'| = Real.sin θ := by
    rw [hθ']; split_ifs
    · exact abs_of_nonneg hsin
    · rw [Real.sin_neg, abs_neg, abs_of_nonneg hsin]
  have hsg : 0 ≤ θ' * s.im := by
    rw [hθ']; split_ifs with h
    · exact mul_nonneg hθ0 h
    · push Not at h; nlinarith
  have h1 := norm_Gr_le s δ (θ := θ') (by rw [habs]; exact hθ) (by linarith) hsg
  rw [habs, hcos, hsin'] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have h2 := integral_rpow_exp_quad_le (p := s.re + 1) (c := Real.cos (2 * θ))
    (b := 2 * π * |δ| * Real.sin θ) (by linarith) (by linarith) hc
  convert h2 using 3 <;> ring

/-! ## The two regimes of [H, Cor 8.0.2] (`k = 2`) -/

theorem sin_028_le : Real.sin 0.28 ≤ 0.27635855 := by
  have h := Real.sin_bound (x := 0.28) (by norm_num [abs_of_pos])
  rw [abs_of_pos (by norm_num : (0:ℝ) < 0.28)] at h
  have := (abs_le.1 h).2
  norm_num at this ⊢; linarith

theorem cos_two_mul_eq (x : ℝ) : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul, Real.cos_sq']; ring

theorem sqrt_consts {c : ℝ} (hc1 : 0.84725 ≤ c) :
    √(π / (c / 2)) ≤ 2.7233 ∧ √π / (c * √(c / 2)) ≤ 3.2143 := by
  have hc0 : 0 < c := by linarith
  have hpi := Real.pi_lt_d6
  constructor
  · rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by positivity)]; nlinarith
  · have h1 : √π ≤ 1.77246 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    have h2 : 0.65086 ≤ √(c / 2) := Real.le_sqrt_of_sq_le (by nlinarith)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hc1 h2 (by norm_num) hc0.le]

/-- **Regime `|τ| ≥ (3/2)(πδ)²`** ([H, Cor 8.0.2], `κ_{2,1}`): `|G_δ(s)| ≤ 0.892 |τ| e^{-0.1598|τ|}`. -/
theorem norm_G_le_regimeB (s : ℂ) (δ : ℝ) (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 1) (hτ : 50 ≤ |s.im|)
    (hδ : 3 / 2 * (π * δ) ^ 2 ≤ |s.im|) :
    ‖Gr s δ 0‖ ≤ 0.892 * |s.im| * Real.exp (-0.1598 * |s.im|) := by
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hθ : (0.28 : ℝ) < π / 4 := by linarith
  have h := norm_Gr_le_closed s δ (θ := 0.28) (by norm_num) hθ hs0 hs1
  have hS := sin_028_le
  have hS0 : 0 ≤ Real.sin 0.28 := Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith)
  have hc := cos_two_mul_eq 0.28
  set S := Real.sin 0.28
  set c := Real.cos (2 * 0.28)
  set τ := |s.im|
  have hS2 : S ^ 2 ≤ 0.0763741 := by nlinarith
  have hc1 : 0.847251 ≤ c := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hδ2 : π ^ 2 * δ ^ 2 ≤ 2 / 3 * τ := by nlinarith
  -- the exponent
  have hb : (2 * π * |δ| * S) ^ 2 / (2 * c) ≤ 0.120192 * τ := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 * π * |δ| * S) ^ 2 = 4 * (π ^ 2 * δ ^ 2) * S ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
    rw [this]
    have hτ0 : 0 ≤ τ := by positivity
    nlinarith [mul_le_mul hδ2 hS2 (sq_nonneg _) (by positivity), mul_le_mul_of_nonneg_left hc1 hτ0]
  -- the prefactor
  have hbc : (2 * π * |δ| * S / c) ^ 2 ≤ 0.28373 * τ := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : (2 * π * |δ| * S) ^ 2 = 4 * (π ^ 2 * δ ^ 2) * S ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
    rw [this]
    have hc2 : 0.717834 ≤ c ^ 2 := by nlinarith
    have hτ0 : 0 ≤ τ := by positivity
    nlinarith [mul_le_mul hδ2 hS2 (sq_nonneg _) (by positivity), mul_le_mul_of_nonneg_left hc2 hτ0]
  obtain ⟨hsq1, hsq2⟩ := sqrt_consts (c := c) (by linarith)
  have hpre : (1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)) ≤ 0.892 * τ := by
    have := mul_le_mul (add_le_add_left hbc 1) hsq1 (Real.sqrt_nonneg _) (by positivity)
    nlinarith
  have hpre0 : 0 ≤ (1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)) := by
    positivity
  refine h.trans ?_
  rw [← mul_assoc, ← Real.exp_add]
  calc Real.exp (-(0.28 * τ) + (2 * π * |δ| * S) ^ 2 / (2 * c)) *
        ((1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)))
      ≤ Real.exp (-0.1598 * τ) * (0.892 * τ) :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith)) hpre hpre0 (Real.exp_pos _).le
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **Regime `|τ| < (3/2)(πδ)²`** ([H, Cor 8.0.2], `κ_{2,0}`): with `y = |τ|/(π|δ|) ≥ 10`,
`|G_δ(s)| ≤ 0.588 y² e^{-0.1065 y²}`. -/
theorem norm_G_le_regimeA (s : ℂ) (δ : ℝ) (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 1)
    (hy : 10 * π * |δ| ≤ |s.im|) (hm : |s.im| < 3 / 2 * (π * δ) ^ 2) :
    ‖Gr s δ 0‖ ≤ 0.588 * (|s.im| / (π * |δ|)) ^ 2 *
      Real.exp (-0.1065 * (|s.im| / (π * |δ|)) ^ 2) := by
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  set τ := |s.im| with hτdef
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hδ0 : δ ≠ 0 := by
    rintro rfl; simp at hm; linarith
  set D := π ^ 2 * δ ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hy2 : (τ / (π * |δ|)) ^ 2 = τ ^ 2 / D := by rw [div_pow, mul_pow, sq_abs δ]
  rw [hy2]
  have hm' : τ < 1.5 * D := by rw [hD]; nlinarith [hm]
  have hyD : 100 * D ≤ τ ^ 2 := by
    have := mul_le_mul hy hy (by positivity) hτ0
    have e : 10 * π * |δ| * (10 * π * |δ|) = 100 * D := by rw [hD, ← sq_abs δ]; ring
    nlinarith
  set θ := 0.1866 * τ / D with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 0.2799 := by rw [hθ, div_le_iff₀ hD0]; nlinarith
  have hθπ : θ < π / 4 := by linarith
  have h := norm_Gr_le_closed s δ hθ0 hθπ hs0 hs1
  have hSb := Real.sin_bound (x := θ) (by rw [abs_of_nonneg hθ0]; linarith)
  rw [abs_of_nonneg hθ0] at hSb
  have hSup := (abs_le.1 hSb).2
  have hS0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hSθ : Real.sin θ ≤ θ := Real.sin_le hθ0
  have hc := cos_two_mul_eq θ
  set S := Real.sin θ with hSdef
  set c := Real.cos (2 * θ) with hcdef
  set u := θ ^ 2 with hu
  have hu1 : u ≤ 0.0783441 := by
    rw [hu]; have := pow_le_pow_left₀ hθ0 hθ1 2; norm_num at this; linarith
  have hu0 : 0 ≤ u := sq_nonneg _
  set B := 1 - 0.165883 * u with hB
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hA : S ≤ θ * B := by
    have h5 : θ ^ 5 / 100 ≤ θ * (0.00078367 * u) := by
      have : θ ^ 5 = θ * u ^ 2 := by rw [hu]; ring
      rw [this]
      nlinarith [mul_nonneg hθ0 (mul_nonneg hu0 (by linarith : (0:ℝ) ≤ 0.078367 - u))]
    have e3 : θ ^ 3 = θ * u := by rw [hu]; ring
    rw [hB]; nlinarith
  have hkey : S ^ 2 * (1 + 2.30042 * u) ≤ 1.15021 * u := by
    have h1 : S ^ 2 ≤ u * B ^ 2 := by
      calc S ^ 2 ≤ (θ * B) ^ 2 := pow_le_pow_left₀ hS0 hA 2
        _ = u * B ^ 2 := by rw [hu]; ring
    have h2 : B ^ 2 * (1 + 2.30042 * u) ≤ 1.15021 := by
      have hq : 0 ≤ 1.968654 - 0.730739 * (u + 0.0783441) := by linarith
      rw [hB]
      nlinarith [mul_nonneg (sub_nonneg.2 hu1) hq, mul_nonneg (mul_nonneg hu0 hu0) (sub_nonneg.2 hu1)]
    have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 1 + 2.30042 * u)
    have h4 := mul_le_mul_of_nonneg_left h2 hu0
    calc S ^ 2 * (1 + 2.30042 * u) ≤ u * B ^ 2 * (1 + 2.30042 * u) := h3
      _ = u * (B ^ 2 * (1 + 2.30042 * u)) := by ring
      _ ≤ u * 1.15021 := h4
      _ = 1.15021 * u := by ring
  have hS2 : S ^ 2 ≤ 0.0763529 := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_le_mul_of_nonneg_left hlt.le hu0]
  have hc1 : 0.84729 ≤ c := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hY : 100 ≤ τ ^ 2 / D := by rw [le_div_iff₀ hD0]; linarith
  have hY0 : 0 ≤ τ ^ 2 / D := by positivity
  have hDu : D * u = 0.1866 ^ 2 * (τ ^ 2 / D) := by
    rw [hu, hθ]; field_simp
  have e4 : (2 * π * |δ| * S) ^ 2 = 4 * D * S ^ 2 := by
    rw [hD, mul_pow, mul_pow, mul_pow, sq_abs]; ring
  -- the exponent
  have hb : (2 * π * |δ| * S) ^ 2 / (2 * c) ≤ 0.0801 * (τ ^ 2 / D) := by
    rw [e4, div_le_iff₀ (by positivity)]
    have hSc : S ^ 2 ≤ 1.15021 * u * c := by rw [hc]; nlinarith
    calc 4 * D * S ^ 2 ≤ 4 * D * (1.15021 * u * c) := by gcongr
      _ = 4.60084 * (D * u) * c := by ring
      _ = 4.60084 * (0.1866 ^ 2 * (τ ^ 2 / D)) * c := by rw [hDu]
      _ ≤ 0.0801 * (τ ^ 2 / D) * (2 * c) := by nlinarith [mul_nonneg hY0 hc0.le]
  have hθτ : θ * τ = 0.1866 * (τ ^ 2 / D) := by rw [hθ]; ring
  -- the prefactor
  have hbc : (2 * π * |δ| * S / c) ^ 2 ≤ 0.19402 * (τ ^ 2 / D) := by
    rw [div_pow, div_le_iff₀ (by positivity), e4]
    have hSu : S ^ 2 ≤ u := by rw [hu]; exact pow_le_pow_left₀ hS0 hSθ 2
    have hc2 : 0.7179 ≤ c ^ 2 := by nlinarith
    calc 4 * D * S ^ 2 ≤ 4 * (D * u) := by nlinarith [mul_le_mul_of_nonneg_left hSu hD0.le]
      _ = 4 * (0.1866 ^ 2 * (τ ^ 2 / D)) := by rw [hDu]
      _ ≤ 0.19402 * (τ ^ 2 / D) * c ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hc2 hY0]
  obtain ⟨hsq1, hsq2⟩ := sqrt_consts (c := c) (by linarith)
  have hpre : (1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)) ≤
      0.588 * (τ ^ 2 / D) := by
    have := mul_le_mul (add_le_add_left hbc 1) hsq1 (Real.sqrt_nonneg _) (by positivity)
    nlinarith
  have hpre0 : 0 ≤ (1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)) := by
    positivity
  refine h.trans ?_
  rw [← mul_assoc, ← Real.exp_add]
  calc Real.exp (-(θ * τ) + (2 * π * |δ| * S) ^ 2 / (2 * c)) *
        ((1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)))
      ≤ Real.exp (-0.1065 * (τ ^ 2 / D)) * (0.588 * (τ ^ 2 / D)) :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith)) hpre hpre0 (Real.exp_pos _).le
    _ = _ := by ring

/-! ## `Gr s δ 0` is the Mellin transform of `t² e^{-t²/2} e(δt)` -/

theorem Gr_zero_eq (s : ℂ) (δ : ℝ) :
    Gr s δ 0 = ∫ t in Ioi (0:ℝ), (t : ℂ) ^ (s - 1) *
      (((t ^ 2 * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * cexp (2 * π * I * δ * t)) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0:ℝ) < t from ht))
  simp only [Jr, Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, mul_one]
  have e1 : (t : ℂ) ^ (s + 1) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ 2 := by
    rw [show s + 1 = (s - 1) + 2 by ring, Complex.cpow_add _ _ ht']
    norm_cast
  rw [e1]
  push_cast
  rw [Complex.exp_add]
  ring_nf

end TernaryGoldbach.Explicit
