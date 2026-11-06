import RSBoundsCompat.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bounds for the digamma function

* Frullani: `∫₀^∞ (e^{−au} − e^{−bu})/u du = log(b/a)`.
* Dirichlet's formula: `ψ(s) = ∫₀^∞ (e^{−u} − (1+u)^{−s}) du/u` for `ℜs > 1/2`.
* `Re ψ(σ+it) − ψ(σ) ≤ ½ log(1 + t²/(σ − ½)²)`, `|Im ψ(σ + it)| ≤ …`, `ψ(σ) ≤ log σ`.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-- `∫_a^b e^{−vu} dv = (e^{−au} − e^{−bu})/u` for `u ≠ 0`. -/
theorem intervalIntegral_exp_neg_mul {u : ℝ} (hu : u ≠ 0) (a b : ℝ) :
    ∫ v in a..b, Real.exp (-(v * u)) = (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u := by
  have hF : ∀ v ∈ [[a, b]], HasDerivAt (fun v => -Real.exp (-(v * u)) / u) (Real.exp (-(v * u))) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => -(v * u)) (-u) v := by
      have := ((hasDerivAt_id v).mul_const u).neg
      simp only [id, one_mul] at this
      exact this
    have h := (h1.exp.neg).div_const u
    convert h using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (-(v * u))).intervalIntegrable _ _)]
  ring

theorem integral_exp_neg_mul_Ioi' {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(v * u)) = 1 / v := by
  have h := integral_exp_mul_Ioi (a := -v) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at h
  rw [h]; field_simp

theorem frullani_pt {a b : ℝ} (hab : a ≤ b) : ∀ u ∈ Ioi (0:ℝ),
    (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u = ∫ v in Ioc a b, Real.exp (-(v * u)) := by
  intro u (hu : 0 < u)
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral_exp_neg_mul hu.ne']

theorem frullani_prod {a b : ℝ} (ha : 0 < a) :
    Integrable (Function.uncurry fun (u v : ℝ) => Real.exp (-(v * u)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc a b))) := by
  have hi : Integrable (fun u : ℝ => Real.exp (-(a * u))) (volume.restrict (Ioi 0)) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    refine this.congr_fun (fun u _ => by ring_nf) measurableSet_Ioi
  have hb' : Integrable (fun p : ℝ × ℝ => Real.exp (-(a * p.1)) * (1 : ℝ))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc a b))) :=
    Integrable.mul_prod hi (integrable_const (1:ℝ))
  refine hb'.mono' (by fun_prop) ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun p hp => ?_)
  have h1 : 0 < p.1 := hp.1
  have h2 : a < p.2 := hp.2.1
  simp only [Function.uncurry, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]
  exact Real.exp_le_exp.2 (by nlinarith)

theorem integrableOn_frullani {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u => (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => ∫ v in Ioc a b, Real.exp (-(v * u))) (Ioi 0) :=
    (frullani_prod (b := b) ha).integral_prod_left
  exact h.congr_fun (fun u hu => (frullani_pt hab u hu).symm) measurableSet_Ioi

/-- **Frullani**: `∫₀^∞ (e^{−au} − e^{−bu})/u du = log(b/a)` for `0 < a ≤ b`. -/
theorem frullani_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in Ioi (0:ℝ), (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u = Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpt := frullani_pt hab
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [integral_integral_swap (frullani_prod ha)]
  rw [setIntegral_congr_fun measurableSet_Ioc fun v (hv : v ∈ Ioc a b) =>
    integral_exp_neg_mul_Ioi' (lt_trans ha hv.1)]
  rw [← intervalIntegral.integral_of_le hab]
  have : ∫ v in a..b, 1 / v = ∫ v in a..b, v⁻¹ := by simp only [one_div]
  rw [this, integral_inv_of_pos ha hb]

/-- **Frullani for `log`**: `∫₀^∞ (e^{−u} − e^{−tu})/u du = log t` for `t > 0`. -/
theorem frullani_log {t : ℝ} (ht : 0 < t) :
    ∫ u in Ioi (0:ℝ), (Real.exp (-u) - Real.exp (-(t * u))) / u = Real.log t := by
  rcases le_total 1 t with h | h
  · have := frullani_of_le one_pos h
    simp only [one_mul, div_one] at this
    exact this
  · have := frullani_of_le ht h
    rw [Real.log_div one_ne_zero ht.ne', Real.log_one, zero_sub] at this
    have e : ∀ u, (Real.exp (-u) - Real.exp (-(t * u))) / u =
        -((Real.exp (-(t * u)) - Real.exp (-(1 * u))) / u) := by intro u; ring_nf
    simp_rw [e, integral_neg, this, neg_neg]

theorem integrableOn_frullani_log {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => (Real.exp (-u) - Real.exp (-(t * u))) / u) (Ioi 0) := by
  rcases le_total 1 t with h | h
  · have := integrableOn_frullani one_pos h
    simpa only [one_mul] using this
  · have := (integrableOn_frullani ht h).neg
    refine this.congr_fun (fun u _ => by simp only [Pi.neg_apply, one_mul]; ring) measurableSet_Ioi

/-- `∫₀^∞ |e^{−u} − e^{−tu}|/u du = |log t|`. -/
theorem integral_abs_frullani {t : ℝ} (ht : 0 < t) :
    ∫ u in Ioi (0:ℝ), |Real.exp (-u) - Real.exp (-(t * u))| / u = |Real.log t| := by
  rcases le_total 1 t with h | h
  · have hpt : ∀ u ∈ Ioi (0:ℝ), |Real.exp (-u) - Real.exp (-(t * u))| / u =
        (Real.exp (-u) - Real.exp (-(t * u))) / u := by
      intro u (hu : 0 < u)
      rw [abs_of_nonneg]
      rw [sub_nonneg]; exact Real.exp_le_exp.2 (by nlinarith)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, frullani_log ht,
      abs_of_nonneg (Real.log_nonneg h)]
  · have hpt : ∀ u ∈ Ioi (0:ℝ), |Real.exp (-u) - Real.exp (-(t * u))| / u =
        -((Real.exp (-u) - Real.exp (-(t * u))) / u) := by
      intro u (hu : 0 < u)
      rw [abs_of_nonpos, neg_div]
      rw [sub_nonpos]; exact Real.exp_le_exp.2 (by nlinarith)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_neg, frullani_log ht,
      abs_of_nonpos (Real.log_nonpos ht.le h)]

/-- `|log t| ≤ t + 2/√t`. -/
theorem abs_log_le_add {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + 2 * t ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  rcases le_total 1 t with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos ht
    linarith
  · rw [abs_of_nonpos (Real.log_nonpos ht.le h)]
    have h1 := Real.log_le_sub_one_of_pos hs
    rw [Real.log_rpow ht] at h1
    linarith

/-! ## Dirichlet's formula -/

/-- The integrand of the double integral. -/
noncomputable def digF (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (s - 1) * ((Real.exp (-p.1) * ((Real.exp (-p.2) - Real.exp (-(p.1 * p.2))) / p.2) : ℝ) : ℂ)

theorem norm_digF {s : ℂ} {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2) :
    ‖digF s p‖ = p.1 ^ (s.re - 1) * (Real.exp (-p.1) * (|Real.exp (-p.2) - Real.exp (-(p.1 * p.2))| / p.2)) := by
  rw [digF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_of_pos h2]
  simp only [Complex.sub_re, Complex.one_re]

theorem continuousOn_digF (s : ℂ) : ContinuousOn (digF s) (Ioi 0 ×ˢ Ioi 0) := by
  intro p hp
  have h1 : (0:ℝ) < p.1 := hp.1
  have h2 : (0:ℝ) < p.2 := hp.2
  unfold digF
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul ?_ ?_
  · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (Complex.ofReal_mem_slitPlane.2 h1)
  · refine Complex.continuous_ofReal.continuousAt.comp ?_
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.div (by fun_prop) (by fun_prop) h2.ne')

theorem integrable_digF {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (digF s) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hmeas : AEStronglyMeasurable (digF s)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (continuousOn_digF s).aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    have h := ((integrableOn_frullani_log ht).norm).const_mul (‖(t : ℂ) ^ (s - 1)‖ * Real.exp (-t))
    refine h.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
      refine ContinuousAt.continuousWithinAt ?_
      have hc : ContinuousAt (fun u : ℝ => Real.exp (-t) * ((Real.exp (-u) - Real.exp (-(t * u))) / u))
          u := ContinuousAt.mul continuousAt_const (ContinuousAt.div (by fun_prop) (by fun_prop) hu.ne')
      show ContinuousAt (fun u : ℝ => (t : ℂ) ^ (s - 1) *
        ((Real.exp (-t) * ((Real.exp (-u) - Real.exp (-(t * u))) / u) : ℝ) : ℂ)) u
      exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hc)
    · refine Eventually.of_forall fun u => ?_
      simp only [digF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos (-t))]
      rw [mul_assoc]
  · have hint : ∀ t ∈ Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), ‖digF s (t, u)‖ =
        t ^ (s.re - 1) * (Real.exp (-t) * |Real.log t|) := by
      intro t (ht : 0 < t)
      rw [setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => norm_digF (s := s)
        (p := (t, u)) ht hu]
      simp only
      rw [integral_const_mul, integral_const_mul, integral_abs_frullani ht]
    have hb : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ ((s.re + 1) - 1) +
        2 * (Real.exp (-t) * t ^ ((s.re - 1 / 2) - 1))) (Ioi 0) :=
      (Real.GammaIntegral_convergent (by linarith)).add
        ((Real.GammaIntegral_convergent (by linarith)).const_mul 2)
    refine (hb.mono' ?_ ?_)
    · refine ((ContinuousOn.aestronglyMeasurable
        (f := fun t : ℝ => t ^ (s.re - 1) * (Real.exp (-t) * |Real.log t|)) ?_ measurableSet_Ioi).congr ?_)
      · exact fun t (ht : 0 < t) => ((Real.continuousAt_rpow_const _ _ (Or.inl ht.ne')).mul
          ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).continuousAt.mul
            (Real.continuousAt_log ht.ne').abs)).continuousWithinAt
      · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => (hint t ht).symm)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
      rw [hint t ht, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hl := abs_log_le_add ht
      have e1 : t ^ (s.re + 1 - 1) = t ^ (s.re - 1) * t := by
        rw [show s.re + 1 - 1 = (s.re - 1) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
      have e2 : t ^ (s.re - 1 / 2 - 1) = t ^ (s.re - 1) * t ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add ht]; congr 1; ring
      rw [e1, e2]
      have h0 : 0 ≤ t ^ (s.re - 1) * Real.exp (-t) := by positivity
      have := mul_le_mul_of_nonneg_left hl h0
      nlinarith

theorem integral_cpow_exp_one_add {s : ℂ} (hs : 0 < s.re) {u : ℝ} (hu : 0 ≤ u) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * (Real.exp (-(t * u)) * Real.exp (-t) : ℝ) =
      ((1 + u : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs (r := 1 + u) (by linarith)
  have e : ∀ t : ℝ, (t : ℂ) ^ (s - 1) * (Real.exp (-(t * u)) * Real.exp (-t) : ℝ) =
      (t : ℂ) ^ (s - 1) * Complex.exp (-(((1 + u : ℝ) : ℂ) * t)) := by
    intro t
    congr 1
    rw [← Real.exp_add]; push_cast; congr 1; ring
  simp_rw [e]
  rw [h]
  congr 1
  have hr : (0:ℝ) < 1 + u := by linarith
  rw [one_div, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

theorem integral_digF_left {s : ℂ} (hs0 : 0 < s.re) {u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ in Ioi 0, digF s (t, u) =
      Complex.Gamma s * (((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-s)) / u) := by
  have i1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ)) (Ioi 0) := by
    refine (Complex.GammaIntegral_convergent hs0).congr_fun (fun t _ => by ring) measurableSet_Ioi
  have i2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      ((Real.exp (-(t * u)) * Real.exp (-t) : ℝ) : ℂ)) (Ioi 0) := by
    refine i1.norm.mono' ?_ ?_
    · exact ContinuousOn.aestronglyMeasurable (fun t (ht : 0 < t) =>
        ((ContinuousAt.cpow (by fun_prop) continuousAt_const
          (Complex.ofReal_mem_slitPlane.2 ht)).mul (by fun_prop)).continuousWithinAt) measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-(t * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have h0 : 0 ≤ ‖(t : ℂ) ^ (s - 1)‖ := norm_nonneg _
      have h1 := Real.exp_pos (-t)
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this h1.le) h0
      linarith
  have e : ∀ t : ℝ, digF s (t, u) = (1 / (u : ℂ)) * ((t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ) *
      (Real.exp (-u) : ℂ) - (t : ℂ) ^ (s - 1) * ((Real.exp (-(t * u)) * Real.exp (-t) : ℝ) : ℂ)) := by
    intro t
    simp only [digF]; push_cast; field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_sub (i1.mul_const _) i2, integral_mul_const,
    integral_cpow_exp_one_add hs0 hu.le]
  have hG : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ) = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs0, Complex.GammaIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; ring
  rw [hG]
  field_simp

/-- **Dirichlet's formula**: `ψ(s) = ∫₀^∞ (e^{−u} − (1+u)^{−s}) du/u` for `ℜs > 1/2`. -/
theorem digamma_eq_integral {s : ℂ} (hs : 1 / 2 < s.re) :
    Complex.digamma s =
      ∫ u : ℝ in Ioi 0, ((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-s)) / u := by
  have hs0 : 0 < s.re := by linarith
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hd := (RSBoundsCompat.Complex.hasDerivAt_Gamma_of_re_pos hs0).deriv
  -- `Γ'(s) = ∫∫ F`
  have hA : deriv Complex.Gamma s = ∫ t : ℝ in Ioi 0, ∫ u : ℝ in Ioi 0, digF s (t, u) := by
    rw [hd]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [digF]
    rw [integral_const_mul, integral_complex_ofReal, integral_const_mul, frullani_log ht]
    push_cast; ring
  have hint : Integrable (Function.uncurry fun t u => digF s (t, u))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := integrable_digF hs
  rw [integral_integral_swap hint] at hA
  -- the inner integrals
  have hB : ∀ u ∈ Ioi (0:ℝ), ∫ t : ℝ in Ioi 0, digF s (t, u) =
      Complex.Gamma s * (((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-s)) / u) :=
    fun u hu => integral_digF_left hs0 hu
  rw [setIntegral_congr_fun measurableSet_Ioi hB, integral_const_mul] at hA
  rw [Complex.digamma_def, logDeriv_apply, hA]
  field_simp

/-! ## Shifts and the sine integral -/

theorem setIntegral_Ioi_one_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ u in Ioi (0:ℝ), f (1 + u) = ∫ y in Ioi (1:ℝ), f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have : (fun u => (Ioi (0:ℝ)).indicator (fun u => f (1 + u)) u) =
      fun u => (Ioi (1:ℝ)).indicator f (u + 1) := by
    ext u
    by_cases hu : 0 < u
    · rw [indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu),
        indicator_of_mem (show u + 1 ∈ Ioi (1:ℝ) by simp only [mem_Ioi]; linarith), add_comm]
    · rw [indicator_of_notMem (show u ∉ Ioi (0:ℝ) from hu),
        indicator_of_notMem (show u + 1 ∉ Ioi (1:ℝ) by simp only [mem_Ioi]; linarith)]
  rw [this, integral_add_right_eq_self (fun y => (Ioi (1:ℝ)).indicator f y) 1]

theorem integrableOn_Ioi_one_add {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntegrableOn f (Ioi 1)) : IntegrableOn (fun u => f (1 + u)) (Ioi 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hf ⊢
  have h := hf.comp_add_right 1
  refine h.congr (Eventually.of_forall fun u => ?_)
  by_cases hu : 0 < u
  · simp only [indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu),
      indicator_of_mem (show u + 1 ∈ Ioi (1:ℝ) by simp only [mem_Ioi]; linarith), add_comm]
  · simp only [indicator_of_notMem (show u ∉ Ioi (0:ℝ) from hu),
      indicator_of_notMem (show u + 1 ∉ Ioi (1:ℝ) by simp only [mem_Ioi]; linarith)]

theorem cpow_one_add_eq {u : ℝ} (hu : 0 ≤ u) (b w : ℝ) :
    (((1 + u : ℝ) : ℂ) ^ ((-b : ℂ) + w * I)) =
      ((1 + u) ^ (-b) : ℝ) * Complex.exp (w * Real.log (1 + u) * I) := by
  have h1 : (0:ℝ) < 1 + u := by linarith
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast h1.ne'), ← Complex.ofReal_log h1.le,
    Real.rpow_def_of_pos h1, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem integrableOn_one_add_cpow {b w : ℝ} (hb : 1 < b) :
    IntegrableOn (fun u : ℝ => ((1 + u : ℝ) : ℂ) ^ ((-b : ℂ) + w * I)) (Ioi 0) := by
  have h := integrableOn_Ioi_cpow_of_lt (a := (-b : ℂ) + w * I) (by simp; linarith) one_pos
  exact integrableOn_Ioi_one_add (f := fun y : ℝ => (y : ℂ) ^ ((-b : ℂ) + w * I)) h

/-- `∫₀^∞ (1+u)^{−b} sin(w log(1+u)) du = w/((b−1)² + w²)` for `b > 1`. -/
theorem integral_one_add_rpow_sin {b : ℝ} (hb : 1 < b) (w : ℝ) :
    ∫ u in Ioi (0:ℝ), (1 + u) ^ (-b) * Real.sin (w * Real.log (1 + u)) = w / ((b - 1) ^ 2 + w ^ 2) := by
  have hpt : ∀ u ∈ Ioi (0:ℝ), (1 + u) ^ (-b) * Real.sin (w * Real.log (1 + u)) =
      (((1 + u : ℝ) : ℂ) ^ ((-b : ℂ) + w * I)).im := by
    intro u (hu : 0 < u)
    rw [cpow_one_add_eq hu.le, Complex.im_ofReal_mul,
      show (w : ℂ) * (Real.log (1 + u) : ℂ) = ((w * Real.log (1 + u) : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_ofReal_mul_I_im]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [show (∫ x in Ioi (0:ℝ), (((1 + x : ℝ) : ℂ) ^ ((-b : ℂ) + w * I)).im) =
      ∫ x in Ioi (0:ℝ), RCLike.im (((1 + x : ℝ) : ℂ) ^ ((-b : ℂ) + w * I)) from rfl,
    integral_im (integrableOn_one_add_cpow hb)]
  rw [setIntegral_Ioi_one_add (fun y : ℝ => (y : ℂ) ^ ((-b : ℂ) + w * I)),
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hne : ((-b : ℂ) + w * I + 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [show RCLike.im (-1 / ((-b : ℂ) + w * I + 1)) = (-1 / ((-b : ℂ) + w * I + 1)).im from rfl,
    Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.normSq_apply]
  have hD : (1 - b) * (1 - b) + w * w ≠ 0 := by nlinarith [sq_nonneg w]
  have hD' : (b - 1) ^ 2 + w ^ 2 ≠ 0 := by nlinarith [sq_nonneg w]
  have e : (-b + (w * 0 - 0 * 1) + 1) * (-b + (w * 0 - 0 * 1) + 1) +
      (-0 + (w * 1 + 0 * 0) + 0) * (-0 + (w * 1 + 0 * 0) + 0) = (b - 1) ^ 2 + w ^ 2 := by ring
  rw [e]
  ring

/-- `(1 − cos(tL))/L = ∫₀^{|t|} sin(wL) dw` for `L ≠ 0`. -/
theorem one_sub_cos_div_eq {L : ℝ} (hL : L ≠ 0) (t : ℝ) :
    (1 - Real.cos (t * L)) / L = ∫ w in (0:ℝ)..|t|, Real.sin (w * L) := by
  have hF : ∀ w ∈ [[(0:ℝ), |t|]], HasDerivAt (fun w => -Real.cos (w * L) / L) (Real.sin (w * L)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => w * L) L w := by
      have := (hasDerivAt_id w).mul_const L
      simp only [id, one_mul] at this
      exact this
    have h := (h1.cos.neg).div_const L
    convert h using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun w : ℝ => Real.sin (w * L)).intervalIntegrable _ _)]
  rcases abs_choice t with h | h <;> rw [h] <;> simp [Real.cos_neg] <;> ring

/-! ## `Re ψ(σ + it) ≤ log σ + ½ log(1 + t²/(σ−1)²)` -/

/-- Dirichlet's integrand. -/
noncomputable def digG (s : ℂ) (u : ℝ) : ℂ := ((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-s)) / u

theorem integrableOn_digG {s : ℂ} (hs : 1 / 2 < s.re) : IntegrableOn (digG s) (Ioi 0) := by
  have hs0 : 0 < s.re := by linarith
  have h : IntegrableOn (fun u : ℝ => ∫ t : ℝ in Ioi 0, digF s (t, u)) (Ioi 0) :=
    (integrable_digF hs).integral_prod_right
  have h2 : IntegrableOn (fun u : ℝ => (Complex.Gamma s)⁻¹ * ∫ t : ℝ in Ioi 0, digF s (t, u)) (Ioi 0) :=
    h.const_mul _
  refine h2.congr_fun (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
  show (Complex.Gamma s)⁻¹ * ∫ t : ℝ in Ioi 0, digF s (t, u) = digG s u
  rw [integral_digF_left hs0 hu, ← mul_assoc, inv_mul_cancel₀ (Complex.Gamma_ne_zero_of_re_pos hs0),
    one_mul, digG]

theorem re_digG {σ t u : ℝ} (hu : 0 < u) :
    (digG ((σ : ℂ) + t * I) u).re =
      (Real.exp (-u) - (1 + u) ^ (-σ) * Real.cos (t * Real.log (1 + u))) / u := by
  have e : -((σ : ℂ) + t * I) = (-σ : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
  rw [digG, e, cpow_one_add_eq hu.le, Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re,
    Complex.re_ofReal_mul, show ((-t : ℝ) : ℂ) * (Real.log (1 + u) : ℂ) =
      ((-t * Real.log (1 + u) : ℝ) : ℂ) by push_cast; ring, Complex.exp_ofReal_mul_I_re,
    show -t * Real.log (1 + u) = -(t * Real.log (1 + u)) by ring, Real.cos_neg]

theorem integrableOn_one_add_rpow {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun u : ℝ => (1 + u) ^ (-σ)) (Ioi 0) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -σ) (by linarith) one_pos
  exact integrableOn_Ioi_one_add (f := fun y : ℝ => y ^ (-σ)) h

/-- The Fubini integrand for the cosine integral. -/
noncomputable def cosF (σ : ℝ) (p : ℝ × ℝ) : ℝ := (1 + p.1) ^ (-σ) * Real.sin (p.2 * Real.log (1 + p.1))

theorem measurable_cosF (σ : ℝ) : Measurable (cosF σ) := by
  unfold cosF
  exact ((measurable_fst.const_add 1).pow_const _).mul
    (Real.measurable_sin.comp (measurable_snd.mul (Real.measurable_log.comp (measurable_fst.const_add 1))))

theorem integrable_cosF {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    Integrable (cosF σ) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc 0 T))) := by
  have hb : Integrable (fun p : ℝ × ℝ => (1 + p.1) ^ (-σ) * (1 : ℝ))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc 0 T))) :=
    Integrable.mul_prod (integrableOn_one_add_rpow hσ) (integrable_const (1:ℝ))
  refine hb.mono' (measurable_cosF σ).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun p hp => ?_)
  have h1 : (0:ℝ) < 1 + p.1 := by have := hp.1; simp only [mem_Ioi] at this; linarith
  rw [cosF, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos h1 _), mul_one]
  exact mul_le_of_le_one_right (Real.rpow_pos_of_pos h1 _).le (Real.abs_sin_le_one _)

/-- `∫₀^∞ (1+u)^{−σ} (1 − cos(t log(1+u)))/log(1+u) du = ½ log(1 + t²/(σ−1)²)` (Fubini). -/
theorem integral_one_add_rpow_cos {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    IntegrableOn (fun u : ℝ => (1 + u) ^ (-σ) * ((1 - Real.cos (t * Real.log (1 + u))) / Real.log (1 + u)))
      (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), (1 + u) ^ (-σ) * ((1 - Real.cos (t * Real.log (1 + u))) / Real.log (1 + u)) =
      1 / 2 * Real.log (1 + t ^ 2 / (σ - 1) ^ 2) := by
  have hprod : Integrable (Function.uncurry fun u w => cosF σ (u, w))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc 0 |t|))) := integrable_cosF hσ |t|
  have hpt : ∀ u ∈ Ioi (0:ℝ), (1 + u) ^ (-σ) * ((1 - Real.cos (t * Real.log (1 + u))) / Real.log (1 + u)) =
      ∫ w in Ioc 0 |t|, cosF σ (u, w) := by
    intro u (hu : 0 < u)
    have hL : Real.log (1 + u) ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [one_sub_cos_div_eq hL t, intervalIntegral.integral_of_le (abs_nonneg t), ← integral_const_mul]
    rfl
  refine ⟨?_, ?_⟩
  · have h : IntegrableOn (fun u : ℝ => ∫ w in Ioc 0 |t|, cosF σ (u, w)) (Ioi 0) :=
      hprod.integral_prod_left
    exact h.congr_fun (fun u hu => (hpt u hu).symm) measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_integral_swap hprod]
  simp only [cosF]
  rw [setIntegral_congr_fun measurableSet_Ioc fun w _ => integral_one_add_rpow_sin hσ w,
    ← intervalIntegral.integral_of_le (abs_nonneg t)]
  have ha : 0 < (σ - 1) ^ 2 := by have : σ - 1 ≠ 0 := by linarith
                                  positivity
  have hG : ∀ w ∈ [[(0:ℝ), |t|]], HasDerivAt (fun w => 1 / 2 * Real.log ((σ - 1) ^ 2 + w ^ 2))
      (w / ((σ - 1) ^ 2 + w ^ 2)) w := by
    intro w _
    have hp : 0 < (σ - 1) ^ 2 + w ^ 2 := by positivity
    have h := (((hasDerivAt_pow 2 w).const_add ((σ - 1) ^ 2)).log hp.ne').const_mul (1 / 2 : ℝ)
    convert h using 1
    field_simp
    push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG (by
    refine ContinuousOn.intervalIntegrable ?_
    exact fun w _ => ((continuousAt_id.div (continuousAt_const.add (continuousAt_id.pow 2))
      (by have : 0 ≤ w ^ 2 := sq_nonneg w
          show (σ - 1) ^ 2 + w ^ 2 ≠ 0
          linarith)).continuousWithinAt))]
  rw [sq_abs, show (0:ℝ) ^ 2 = 0 by norm_num, add_zero, ← mul_sub,
    ← Real.log_div (by positivity) ha.ne']
  congr 2
  field_simp

/-- **`Re ψ(σ + it) ≤ log σ + ½ log(1 + t²/(σ−1)²)`** for `σ > 1`. -/
theorem re_digamma_le {σ t : ℝ} (hσ : 1 < σ) :
    (Complex.digamma ((σ : ℂ) + t * I)).re ≤ Real.log σ + 1 / 2 * Real.log (1 + t ^ 2 / (σ - 1) ^ 2) := by
  have hs : 1 / 2 < ((σ : ℂ) + t * I).re := by simp; linarith
  have hσ0 : 0 < σ := by linarith
  rw [digamma_eq_integral hs]
  have hint := integrableOn_digG hs
  rw [show (∫ u : ℝ in Ioi 0, ((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))) / u).re =
      RCLike.re (∫ u : ℝ in Ioi 0, digG ((σ : ℂ) + t * I) u) from rfl, ← integral_re hint]
  obtain ⟨hJi, hJ⟩ := integral_one_add_rpow_cos hσ t
  have hFr := integrableOn_frullani (a := 1) (b := σ) one_pos hσ.le
  have hFv := frullani_of_le (a := 1) (b := σ) one_pos hσ.le
  simp only [one_mul, div_one] at hFr hFv
  have hpt : ∀ u ∈ Ioi (0:ℝ), RCLike.re (digG ((σ : ℂ) + t * I) u) ≤
      (Real.exp (-u) - Real.exp (-(σ * u))) / u +
        (1 + u) ^ (-σ) * ((1 - Real.cos (t * Real.log (1 + u))) / Real.log (1 + u)) := by
    intro u (hu : 0 < u)
    rw [show RCLike.re (digG ((σ : ℂ) + t * I) u) = (digG ((σ : ℂ) + t * I) u).re from rfl, re_digG hu]
    have hL0 : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
    have hLu : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + u by linarith); linarith
    have h1 : Real.exp (-(σ * u)) ≤ (1 + u) ^ (-σ) := by
      rw [Real.rpow_neg (by linarith), ← Real.exp_log (show (0:ℝ) < 1 + u by linarith),
        ← Real.exp_mul, ← Real.exp_neg]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hc : 0 ≤ 1 - Real.cos (t * Real.log (1 + u)) := by linarith [Real.cos_le_one (t * Real.log (1 + u))]
    have hr : 0 ≤ (1 + u) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have h2 : (1 + u) ^ (-σ) * (1 - Real.cos (t * Real.log (1 + u))) / u ≤
        (1 + u) ^ (-σ) * ((1 - Real.cos (t * Real.log (1 + u))) / Real.log (1 + u)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hc hL0 hLu) hr
    have e : (Real.exp (-u) - (1 + u) ^ (-σ) * Real.cos (t * Real.log (1 + u))) / u =
        (Real.exp (-u) - Real.exp (-(σ * u))) / u + (Real.exp (-(σ * u)) - (1 + u) ^ (-σ)) / u +
          (1 + u) ^ (-σ) * (1 - Real.cos (t * Real.log (1 + u))) / u := by
      field_simp; ring
    rw [e]
    have h3 : (Real.exp (-(σ * u)) - (1 + u) ^ (-σ)) / u ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hu.le
    linarith
  refine (setIntegral_mono_on hint.re (hFr.add hJi) measurableSet_Ioi hpt).trans (le_of_eq ?_)
  simp only [Pi.add_apply]
  rw [integral_add hFr hJi, hFv, hJ]

/-- **`Re ψ(x + iy) ≤ log(x+1) + ½ log(1 + y²/x²)`** for `x > 0` (via `ψ(z) = ψ(z+1) − 1/z`). -/
theorem re_digamma_le' {x y : ℝ} (hx : 0 < x) :
    (Complex.digamma ((x : ℂ) + y * I)).re ≤ Real.log (x + 1) + 1 / 2 * Real.log (1 + y ^ 2 / x ^ 2) := by
  set z : ℂ := (x : ℂ) + y * I with hz
  have hz0 : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [hz] at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one z hz0
  have h1 : (Complex.digamma (z + 1)).re ≤
      Real.log (x + 1) + 1 / 2 * Real.log (1 + y ^ 2 / (x + 1 - 1) ^ 2) := by
    have e : z + 1 = ((x + 1 : ℝ) : ℂ) + y * I := by rw [hz]; push_cast; ring
    rw [e]; exact re_digamma_le (by linarith)
  rw [show x + 1 - 1 = x by ring] at h1
  have h2 : 0 ≤ (z⁻¹).re := by
    rw [Complex.inv_re]; apply div_nonneg _ (Complex.normSq_nonneg _); simp [hz]; linarith
  have : (Complex.digamma z).re = (Complex.digamma (z + 1)).re - (z⁻¹).re := by
    rw [hrec, Complex.add_re]; ring
  linarith

/-- For the zero-free region: `½ Re ψ(s/2) ≤ ½ log|t| + 0.36` for `s = σ + it`, `1 < σ ≤ 2`, `|t| ≥ 10`. -/
theorem half_re_digamma_half_le {σ t : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (ht : 10 ≤ |t|) :
    1 / 2 * (Complex.digamma (((σ : ℂ) + t * I) / 2)).re ≤ 1 / 2 * Real.log |t| + 0.36 := by
  have e : ((σ : ℂ) + t * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  have h := re_digamma_le' (x := σ / 2) (y := t / 2) (by linarith)
  have hl1 : Real.log (σ / 2 + 1) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hq : 1 + (t / 2) ^ 2 / (σ / 2) ^ 2 ≤ t ^ 2 * 1.01 := by
    rw [div_pow, div_pow, div_div_div_cancel_right₀ (by norm_num : (2:ℝ) ^ 2 ≠ 0)]
    have hσ2 : 1 ≤ σ ^ 2 := by nlinarith
    have ht2 : 100 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
    have : t ^ 2 / σ ^ 2 ≤ t ^ 2 := div_le_self (sq_nonneg t) hσ2
    linarith
  have hq0 : 0 < 1 + (t / 2) ^ 2 / (σ / 2) ^ 2 := by positivity
  have hl3 : Real.log (1 + (t / 2) ^ 2 / (σ / 2) ^ 2) ≤ 2 * Real.log |t| + Real.log 1.01 := by
    have ht0 : 0 < |t| := by linarith
    refine (Real.log_le_log hq0 hq).trans (le_of_eq ?_)
    have htne : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; norm_num at ht
    rw [Real.log_mul (pow_ne_zero 2 htne) (by norm_num), ← sq_abs, Real.log_pow]; push_cast; ring
  have hl4 : Real.log 1.01 ≤ 0.01 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1.01 by norm_num); linarith
  nlinarith

/-! ## A crude bound `|ψ(z)| ≤ 16 log(1 + |z|)` -/

/-- `|e^w − 1| ≤ |w|` for `ℜw ≤ 0`. -/
theorem norm_exp_sub_one_le_of_re_nonpos {w : ℂ} (hw : w.re ≤ 0) : ‖Complex.exp w - 1‖ ≤ ‖w‖ := by
  have hF : ∀ t ∈ [[(0:ℝ), 1]], HasDerivAt (fun t : ℝ => Complex.exp (t * w)) (w * Complex.exp (t * w)) t := by
    intro t _
    have h := ((hasDerivAt_id (t : ℂ)).mul_const w).cexp.comp_ofReal
    simp only [id, one_mul] at h
    convert h using 1; ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun t : ℝ => w * Complex.exp (t * w)).intervalIntegrable _ _)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hint
  rw [← hint]
  have hb : ∀ t ∈ Ι (0:ℝ) 1, ‖w * Complex.exp (t * w)‖ ≤ ‖w‖ := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [norm_mul, Complex.norm_exp]
    have : (t * w : ℂ).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos ht.1.le hw
    calc ‖w‖ * Real.exp ((t * w : ℂ).re) ≤ ‖w‖ * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 this) (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

theorem integral_inv_one_add_mul {b : ℝ} (hb : 1 < b) :
    IntegrableOn (fun u : ℝ => 1 / ((1 + b * u) * (1 + u))) (Ioi 0) ∧
      ∫ u in Ioi (0:ℝ), 1 / ((1 + b * u) * (1 + u)) = Real.log b / (b - 1) := by
  set F : ℝ → ℝ := fun u => (Real.log (1 + b * u) - Real.log (1 + u)) / (b - 1) with hF
  have hb1 : (0:ℝ) < b - 1 := by linarith
  have hd : ∀ x ∈ Ici (0:ℝ), HasDerivAt F (1 / ((1 + b * x) * (1 + x))) x := by
    intro x (hx : 0 ≤ x)
    have h1 : 0 < 1 + b * x := by nlinarith
    have h2 : 0 < 1 + x := by linarith
    have hx1 : HasDerivAt (fun x : ℝ => 1 + b * x) b x := by
      simpa using ((hasDerivAt_id x).const_mul b).const_add 1
    have hx2 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    have h := ((hx1.log h1.ne').sub (hx2.log h2.ne')).div_const (b - 1)
    exact h.congr_deriv (by field_simp; ring)
  have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ 1 / ((1 + b * x) * (1 + x)) := by
    intro x (hx : 0 < x)
    have h1 : 0 < 1 + b * x := by nlinarith
    have h2 : 0 < 1 + x := by linarith
    positivity
  have hlim : Tendsto F atTop (𝓝 (Real.log b / (b - 1))) := by
    have e : ∀ u : ℝ, 0 < u → F u = Real.log ((1 + b * u) / (1 + u)) / (b - 1) := by
      intro u hu
      rw [hF, Real.log_div (by nlinarith) (by linarith)]
    have hq : Tendsto (fun u : ℝ => (1 + b * u) / (1 + u)) atTop (𝓝 b) := by
      have : (fun u : ℝ => (1 + b * u) / (1 + u)) =ᶠ[atTop] fun u => b + (1 - b) / (1 + u) := by
        filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
        field_simp; ring
      rw [tendsto_congr' this]
      have h2 : Tendsto (fun u : ℝ => (1 - b) / (1 + u)) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_left _ 1 tendsto_id)
      simpa using h2.const_add b
    have hl := ((Real.continuousAt_log (by linarith : b ≠ 0)).tendsto.comp hq).div_const (b - 1)
    refine hl.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    exact (e u hu).symm
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim) hlim]
  simp [hF]

/-- **`|ψ(z)| ≤ 16 log(1 + |z|)`** for `ℜz ≥ 1`, `|z| ≥ 3`. -/
theorem norm_digamma_le {z : ℂ} (hx : 1 ≤ z.re) (hz : 3 ≤ ‖z‖) :
    ‖Complex.digamma z‖ ≤ 16 * Real.log (1 + ‖z‖) := by
  set A := 1 + ‖z‖ with hA
  have hA4 : 4 ≤ A := by linarith
  have hs : 1 / 2 < z.re := by linarith
  rw [digamma_eq_integral hs]
  obtain ⟨hMi, hMv⟩ := integral_inv_one_add_mul (b := A / 2) (by linarith)
  have hpt : ∀ u ∈ Ioi (0:ℝ), ‖digG z u‖ ≤ 4 * A * (1 / ((1 + A / 2 * u) * (1 + u))) := by
    intro u (hu : 0 < u)
    have h1u : (0:ℝ) < 1 + u := by linarith
    have hL : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos h1u; linarith
    have hL0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
    -- `|(1+u)^{−z}| ≤ (1+u)^{−1}`
    have hcp : ((1 + u : ℝ) : ℂ) ^ (-z) = Complex.exp (-z * Real.log (1 + u)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast h1u.ne'), ← Complex.ofReal_log h1u.le]; ring_nf
    have hcpn : ‖((1 + u : ℝ) : ℂ) ^ (-z)‖ ≤ 1 / (1 + u) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos h1u, Complex.neg_re, Real.rpow_neg h1u.le, one_div]
      exact inv_anti₀ h1u (Real.self_le_rpow_of_one_le (by linarith) hx)
    have hexp : Real.exp (-u) ≤ 1 / (1 + u) := by
      rw [Real.exp_neg, one_div]; exact inv_anti₀ h1u (by linarith [Real.add_one_le_exp u])
    -- bound (a): `|g| ≤ A`
    have ha : ‖digG z u‖ ≤ A := by
      rw [digG, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, div_le_iff₀ hu]
      have e : (Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-z) =
          ((Real.exp (-u) : ℂ) - 1) - (Complex.exp (-z * Real.log (1 + u)) - 1) := by rw [hcp]; ring
      rw [e]
      have h1 : ‖(Real.exp (-u) : ℂ) - 1‖ ≤ u := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 (by linarith : -u ≤ 0)])]
        linarith [Real.add_one_le_exp (-u)]
      have h2 : ‖Complex.exp (-z * Real.log (1 + u)) - 1‖ ≤ ‖z‖ * u := by
        refine (norm_exp_sub_one_le_of_re_nonpos ?_).trans ?_
        · simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
            Complex.ofReal_im, mul_zero, sub_zero]
          nlinarith
        · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
          exact mul_le_mul_of_nonneg_left hL (norm_nonneg _)
      calc ‖((Real.exp (-u) : ℂ) - 1) - (Complex.exp (-z * Real.log (1 + u)) - 1)‖
          ≤ ‖(Real.exp (-u) : ℂ) - 1‖ + ‖Complex.exp (-z * Real.log (1 + u)) - 1‖ := norm_sub_le _ _
        _ ≤ u + ‖z‖ * u := add_le_add h1 h2
        _ = A * u := by rw [hA]; ring
    -- bound (b): `|g| ≤ 2/(u(1+u))`
    have hb : ‖digG z u‖ ≤ 2 / (u * (1 + u)) := by
      rw [digG, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
      have := norm_sub_le (Real.exp (-u) : ℂ) (((1 + u : ℝ) : ℂ) ^ (-z))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
      rw [div_le_div_iff₀ hu (by positivity)]
      have hN : ‖(Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-z)‖ ≤ 2 / (1 + u) := by
        have e : (2:ℝ) / (1 + u) = 1 / (1 + u) + 1 / (1 + u) := by ring
        linarith
      rw [le_div_iff₀ h1u] at hN
      nlinarith
    have hM0 : 0 < (1 + A / 2 * u) * (1 + u) := by positivity
    rcases le_or_gt (A * u) 2 with hc | hc
    · refine ha.trans ?_
      rw [mul_one_div, le_div_iff₀ hM0]
      have hu2 : u ≤ 1 / 2 := by nlinarith
      have hp1 : 1 + A / 2 * u ≤ 2 := by nlinarith
      have hp2 : (1 + A / 2 * u) * (1 + u) ≤ 2 * (3 / 2) :=
        mul_le_mul hp1 (by linarith) (by linarith) (by norm_num)
      nlinarith
    · refine hb.trans ?_
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hM0]
      nlinarith
  have hint := (integrableOn_digG hs).norm
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (setIntegral_mono_on hint (hMi.const_mul (4 * A)) measurableSet_Ioi hpt).trans ?_
  rw [integral_const_mul, hMv]
  have hlog : 0 ≤ Real.log (A / 2) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (A / 2) ≤ Real.log A := Real.log_le_log (by linarith) (by linarith)
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith

end TernaryGoldbach.Explicit
