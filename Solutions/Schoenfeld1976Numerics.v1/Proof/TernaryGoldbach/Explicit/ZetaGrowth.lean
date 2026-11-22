import TernaryGoldbach.Explicit.Datum

/-!
# `(s − 1)ζ(s)`: an entire function, and its growth on `ℜs > 0`

`zetaF = (s − 1)ζ(s)`, extended by `1` at `s = 1` (`riemannZeta_residue_one`), is entire. Abel summation
with the sawtooth `⌊t⌋ − t` gives `zetaF(s) = s + s(s − 1) ∫₁^∞ (⌊t⌋ − t) t^{−s−1} dt` on `ℜs > 0`, hence
`|zetaF(s)| ≤ |s| + |s||s − 1|/ℜs`.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace TernaryGoldbach.Explicit

/-- `(s − 1)ζ(s)`, extended by `1` at `s = 1`. -/
noncomputable def zetaF : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1

theorem zetaF_of_ne {s : ℂ} (hs : s ≠ 1) : zetaF s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

theorem zetaF_one : zetaF 1 = 1 := Function.update_self _ _ _

theorem differentiableAt_zetaF_of_ne {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ zetaF s := by
  have : zetaF =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht using zetaF_of_ne ht
  exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
    this

theorem differentiable_zetaF : Differentiable ℂ zetaF := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact differentiableAt_zetaF_of_ne hs
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact differentiableAt_zetaF_of_ne ht
    · simpa only [zetaF, continuousAt_update_same] using riemannZeta_residue_one

/-! ## The sawtooth integral -/

/-- `⌊t⌋ − t`. -/
noncomputable def saw (t : ℝ) : ℂ := ((⌊t⌋₊ : ℝ) : ℂ) - t

theorem norm_saw_le {t : ℝ} (ht : 0 ≤ t) : ‖saw t‖ ≤ 1 := by
  rw [saw, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (by linarith [Nat.floor_le ht])]
  linarith [Nat.lt_floor_add_one t]

theorem measurable_saw : Measurable saw := by
  unfold saw
  exact (Complex.measurable_ofReal.comp (measurable_from_nat.comp Nat.measurable_floor)).sub
    Complex.measurable_ofReal

/-- `∫₁^∞ (⌊t⌋ − t) t^{−s−1} dt`. -/
noncomputable def Izeta (s : ℂ) : ℂ := ∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-(s + 1))

theorem aesm_saw_integrand (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) := by
  refine measurable_saw.aestronglyMeasurable.mul ?_
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const t _
    (Or.inr (by have : (1:ℝ) < t := ht; positivity))).continuousWithinAt

theorem integrableOn_saw_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  refine ((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul
    (1 : ℝ)).mono' (aesm_saw_integrand s) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : (0:ℝ) < t := lt_trans one_pos ht
  rw [norm_mul, norm_cpow_neg ht']
  exact mul_le_mul_of_nonneg_right (norm_saw_le ht'.le) (Real.rpow_nonneg ht'.le _)

theorem hasDerivAt_Izeta {s₀ : ℂ} (hs : 0 < s₀.re) :
    HasDerivAt Izeta (∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-(s₀ + 1)) * (-(Real.log t : ℂ))) s₀ := by
  set σ₀ := s₀.re
  have hball : ∀ s ∈ Metric.ball s₀ (σ₀ / 2), σ₀ / 2 < s.re := fun s hs' => by
    rw [Metric.mem_ball, dist_eq_norm] at hs'
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le (s.re - s₀.re)]
  have hbd : IntegrableOn (fun t : ℝ => (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun s t => saw t * (t : ℂ) ^ (-(s + 1)))
    (F' := fun s t => saw t * (t : ℂ) ^ (-(s + 1)) * (-(Real.log t : ℂ))) (x₀ := s₀)
    (bound := fun t => (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1))
    (Metric.ball_mem_nhds s₀ (half_pos hs))
    (Filter.Eventually.of_forall fun s => aesm_saw_integrand s)
    (integrableOn_saw_integrand hs)
    ((aesm_saw_integrand s₀).mul
      (Complex.measurable_ofReal.comp Real.measurable_log).neg.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht s hs' => by
      have ht' : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := by linarith
      have hσ := hball s hs'
      rw [norm_mul, norm_mul, norm_cpow_neg ht0, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg ht'.le)]
      have hlog : Real.log t ≤ t ^ (σ₀ / 4) / (σ₀ / 4) := Real.log_le_rpow_div ht0.le (by positivity)
      have hpow : t ^ (-(s.re + 1)) ≤ t ^ (-(σ₀ / 2) - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht'.le (by linarith)
      have e : t ^ (-(σ₀ / 2) - 1) * (t ^ (σ₀ / 4) / (σ₀ / 4)) = (4 / σ₀) * t ^ (-(σ₀ / 4) - 1) := by
        rw [mul_div_assoc', ← Real.rpow_add ht0, show -(σ₀ / 2) - 1 + σ₀ / 4 = -(σ₀ / 4) - 1 by ring]
        field_simp
      calc ‖saw t‖ * t ^ (-(s.re + 1)) * Real.log t
          ≤ (1 : ℝ) * t ^ (-(σ₀ / 2) - 1) * (t ^ (σ₀ / 4) / (σ₀ / 4)) :=
            mul_le_mul (mul_le_mul (norm_saw_le ht0.le) hpow (Real.rpow_nonneg ht0.le _)
              (by positivity)) hlog (Real.log_nonneg ht'.le) (by positivity)
          _ = (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1) := by rw [mul_assoc, e]; ring))
    hbd
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht s _ => by
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht
      have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have h1 : HasDerivAt (fun s : ℂ => -(s + 1)) (-1) s := ((hasDerivAt_id s).add_const 1).neg
      refine ((h1.const_cpow (Or.inl ht0')).const_mul (saw t)).congr_deriv ?_
      rw [← Complex.ofReal_log ht0.le]; ring))
  exact h.2

/-- `ζ(s) = s/(s − 1) + s Izeta(s)` for `ℜs > 1`. -/
theorem riemannZeta_eq_Izeta {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) + s * Izeta s := by
  have hs0 : 0 < s.re := by linarith
  rw [← LSeries_one_eq_riemannZeta hs]
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    simp
  have hsum : LSeriesSummable 1 s := by
    rw [show (1 : ℕ → ℂ) = fun _ => 1 from rfl]
    exact (LSeriesSummable_one_iff).2 hs
  rw [LSeries_eq_mul_integral _ zero_le_one hs hsum hO]
  have e1 : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = ((⌊t⌋₊ : ℝ) : ℂ) := by
    intro t; simp
  simp_rw [e1]
  have hI1 : IntegrableOn (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_saw_integrand hs0
  have hI2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have e2 : ∀ t ∈ Ioi (1:ℝ), ((⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      saw t * (t : ℂ) ^ (-(s + 1)) + (t : ℂ) ^ (-s) := by
    intro t ht
    have ht' : (0:ℝ) < t := lt_trans one_pos ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
    rw [saw, sub_mul, show (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) by
      rw [show -s = 1 + -(s + 1) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_add hI1 hI2,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos, Complex.ofReal_one, Complex.one_cpow]
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1' : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  rw [Izeta]
  field_simp
  ring

/-- **`zetaF(s) = s + s(s − 1) Izeta(s)`** for `ℜs > 0`. -/
theorem zetaF_eq {s : ℂ} (hs : 0 < s.re) : zetaF s = s + s * (s - 1) * Izeta s := by
  set U := {s : ℂ | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ zetaF U := fun z _ => differentiable_zetaF.analyticAt z
  have hg : AnalyticOnNhd ℂ (fun s => s + s * (s - 1) * Izeta s) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact (differentiableAt_id.add ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (hasDerivAt_Izeta hz).differentiableAt)).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := by show (0:ℝ) < (2:ℂ).re; norm_num
  have hev : zetaF =ᶠ[nhds (2 : ℂ)] fun s => s + s * (s - 1) * Izeta s := by
    have hopen : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show (1:ℝ) < (2:ℂ).re; norm_num)
    filter_upwards [hopen] with s hs1
    have hne : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hne
    rw [zetaF_of_ne hne, riemannZeta_eq_Izeta hs1]
    field_simp
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2 hev hs

/-- **`|(s − 1)ζ(s)| ≤ |s| + |s||s − 1|/ℜs`** for `ℜs > 0`. -/
theorem norm_zetaF_le {s : ℂ} (hs : 0 < s.re) : ‖zetaF s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [zetaF_eq hs]
  have hb : ‖Izeta s‖ ≤ 1 / s.re := by
    have hi := (integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul (1 : ℝ)
    refine (norm_integral_le_of_norm_le hi ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
    · have ht' : (0:ℝ) < t := lt_trans one_pos ht
      rw [norm_mul, norm_cpow_neg ht']
      exact mul_le_mul_of_nonneg_right (norm_saw_le ht'.le) (Real.rpow_nonneg ht'.le _)
    · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
        show -(s.re + 1) + 1 = -s.re by ring]
      have : s.re ≠ 0 := hs.ne'
      field_simp
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ ‖s‖ * ‖s - 1‖)
  rw [mul_one_div] at this
  linarith

/-! ## The left half: the functional equation -/

theorem Gamma_le_40320 {x : ℝ} (h1 : 3 / 4 ≤ x) (h2 : x ≤ 9) : Real.Gamma x ≤ 40320 := by
  have h34 : Real.Gamma (3 / 4) ≤ 24 := Gamma_le_24 (by norm_num) (by norm_num)
  have h9 : Real.Gamma 9 = 40320 := by
    rw [show (9:ℝ) = ((8:ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have h := Real.convexOn_Gamma.le_max_of_mem_segment (x := 3 / 4) (y := 9) (z := x)
    (by norm_num) (by norm_num) (by rw [segment_eq_Icc (by norm_num)]; exact ⟨h1, h2⟩)
  rw [h9] at h
  exact h.trans (max_le (by linarith) le_rfl)

/-- `|sin z| ≤ 1.18 |z| e^{|ℑz|}`. -/
theorem norm_sin_le_mul (z : ℂ) : ‖Complex.sin z‖ ≤ 1.18 * ‖z‖ * Real.exp |z.im| := by
  have he : 1 ≤ Real.exp |z.im| := Real.one_le_exp (abs_nonneg _)
  by_cases h : ‖z‖ ≤ 1
  · have hb := Complex.sin_bound h
    have h1 : ‖Complex.sin z‖ ≤ ‖z - z ^ 3 / 6‖ + ‖z‖ ^ 5 / 100 := by
      have := norm_sub_norm_le (Complex.sin z) (z - z ^ 3 / 6); linarith
    have h2 : ‖z - z ^ 3 / 6‖ ≤ ‖z‖ + ‖z‖ ^ 3 / 6 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_div, norm_pow]; norm_num
    have hz0 := norm_nonneg z
    have h3 : ‖z‖ ^ 3 ≤ ‖z‖ := by nlinarith [pow_le_one₀ hz0 h (n := 2)]
    have h5 : ‖z‖ ^ 5 ≤ ‖z‖ := by nlinarith [pow_le_one₀ hz0 h (n := 4)]
    nlinarith
  · push Not at h
    refine (norm_sin_le_exp z).trans ?_
    nlinarith [Real.exp_pos |z.im|]

/-- The functional equation for `zetaF`: for `w ≠ 0`, `ℜw ≤ 1/4`,
`zetaF(w) = (w − 1) · 2 (2π)^{w−1} Γ(1−w) sin(πw/2) · zetaF(1 − w)/(−w)`. -/
theorem zetaF_left_eq {w : ℂ} (hw0 : w ≠ 0) (hre : w.re ≤ 1 / 4) :
    zetaF w = (w - 1) * (2 * (2 * π) ^ (-(1 - w)) * Complex.Gamma (1 - w) *
      Complex.sin (π * w / 2) * (zetaF (1 - w) / (-w))) := by
  have hw1 : w ≠ 1 := by intro h; rw [h] at hre; simp at hre; linarith
  have h1w : 1 - w ≠ 1 := by intro h; apply hw0; linear_combination -h
  have hFE := riemannZeta_one_sub (s := 1 - w) (fun n h => by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) h1w
  rw [show 1 - (1 - w) = w by ring] at hFE
  rw [zetaF_of_ne hw1, hFE, zetaF_of_ne h1w]
  have hcos : Complex.cos (π * (1 - w) / 2) = Complex.sin (π * w / 2) := by
    rw [show (π : ℂ) * (1 - w) / 2 = π / 2 - π * w / 2 by ring, Complex.cos_pi_div_two_sub]
  rw [hcos]
  field_simp
  ring

/-- **Growth on the left**: for `−8 ≤ ℜw ≤ 1/4`,
`|zetaF(w)| ≤ 1.18·π·40320 · |w − 1| e^{π|ℑw|/2} (|1 − w| + |1 − w||w|/(1 − ℜw))`. -/
theorem norm_zetaF_left {w : ℂ} (h1 : -8 ≤ w.re) (h2 : w.re ≤ 1 / 4) :
    ‖zetaF w‖ ≤ 1.18 * π * 40320 * ‖w - 1‖ * Real.exp (π * |w.im| / 2) *
      (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re)) := by
  have hpi := Real.pi_gt_three
  have hR0 : 0 < 1 - w.re := by linarith
  by_cases hw0 : w = 0
  · subst hw0
    have h0 : zetaF 0 = 1 / 2 := by
      rw [zetaF_of_ne (by norm_num), riemannZeta_zero]; norm_num
    rw [h0]
    simp only [zero_sub, norm_neg, norm_one, Complex.zero_im, abs_zero, mul_zero, zero_div,
      Real.exp_zero, mul_one, sub_zero, norm_zero, Complex.zero_re, div_one, add_zero]
    norm_num
    nlinarith
  rw [zetaF_left_eq hw0 h2]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hcp : ‖(2 * (π : ℂ)) ^ (-(1 - w))‖ ≤ 1 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    simp; linarith
  have hG : ‖Complex.Gamma (1 - w)‖ ≤ 40320 := by
    have hre1 : (1 - w).re = 1 - w.re := by simp
    refine (norm_Gamma_le_Gamma_re (by rw [hre1]; linarith)).trans ?_
    rw [hre1]; exact Gamma_le_40320 (by linarith) (by linarith)
  have hsin : ‖Complex.sin (π * w / 2)‖ ≤ 1.18 * (π / 2 * ‖w‖) * Real.exp (π * |w.im| / 2) := by
    refine (norm_sin_le_mul _).trans (le_of_eq ?_)
    have hn : ‖(π : ℂ) * w / 2‖ = π / 2 * ‖w‖ := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num; ring
    have him : ((π : ℂ) * w / 2).im = π * w.im / 2 := by simp
    rw [hn, him, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  have hZ : ‖zetaF (1 - w)‖ ≤ ‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re) := by
    have hre1 : (1 - w).re = 1 - w.re := by simp
    have := norm_zetaF_le (s := 1 - w) (by rw [hre1]; linarith)
    rwa [hre1, show (1 - w - 1) = -w by ring, norm_neg] at this
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_div, norm_neg, Complex.norm_ofNat]
  have hZ0 : 0 ≤ ‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re) := by positivity
  have hE := Real.exp_pos (π * |w.im| / 2)
  calc ‖w - 1‖ * (2 * ‖(2 * (π : ℂ)) ^ (-(1 - w))‖ * ‖Complex.Gamma (1 - w)‖ *
        ‖Complex.sin (π * w / 2)‖ * (‖zetaF (1 - w)‖ / ‖w‖))
      = ‖w - 1‖ * (2 * ‖(2 * (π : ℂ)) ^ (-(1 - w))‖ * ‖Complex.Gamma (1 - w)‖ *
          (‖Complex.sin (π * w / 2)‖ / ‖w‖) * ‖zetaF (1 - w)‖) := by ring
    _ ≤ ‖w - 1‖ * (2 * 1 * 40320 * (1.18 * (π / 2) * Real.exp (π * |w.im| / 2)) *
          (‖1 - w‖ + ‖1 - w‖ * ‖w‖ / (1 - w.re))) := by
        gcongr
        rw [div_le_iff₀ hwn]
        calc ‖Complex.sin (π * w / 2)‖ ≤ 1.18 * (π / 2 * ‖w‖) * Real.exp (π * |w.im| / 2) := hsin
          _ = _ := by ring
    _ = _ := by ring

end TernaryGoldbach.Explicit
