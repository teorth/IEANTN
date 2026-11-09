import TernaryGoldbach.Prelim.GaussInduced
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor

/-!
# Growth of `L(s, χ)` in `ℜs > 0` (`χ ≠ 1`)

`L(s, χ) = s ∫₁^∞ S(t) t^{-s-1} dt` for `ℜs > 0`, where `S(t) = Σ_{1 ≤ k ≤ t} χ(k)` (by the identity
theorem from `ℜs > 1`, where it is Abel summation), and `|S(t)| ≤ q + 1`. Hence
`|L(s, χ)| ≤ (q + 1)|s|/ℜs`.
-/

open Complex MeasureTheory Set Filter
open Finset (range Icc)

namespace TernaryGoldbach.Explicit

variable {q : ℕ} [NeZero q]

theorem sum_range_shift_eq_zero {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (m : ℕ) :
    ∑ k ∈ range q, χ ((m + k : ℕ) : ZMod q) = 0 := by
  induction m with
  | zero =>
    simp only [zero_add]
    rw [← TernaryGoldbach.sum_zmod_eq_sum_range]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  | succ m ih =>
    have h1 := Finset.sum_range_succ (fun k => χ ((m + k : ℕ) : ZMod q)) q
    have h2 := Finset.sum_range_succ' (fun k => χ ((m + k : ℕ) : ZMod q)) q
    have hper : ((m + q : ℕ) : ZMod q) = ((m + 0 : ℕ) : ZMod q) := by
      push_cast; simp
    rw [ih, zero_add, hper] at h1
    have e : ∀ k, ((m + (k + 1) : ℕ) : ZMod q) = ((m + 1 + k : ℕ) : ZMod q) := fun k => by
      congr 1; ring
    simp only [e] at h2
    rw [h1] at h2
    linear_combination -h2

theorem sum_range_mul_eq_zero {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (a : ℕ) :
    ∑ k ∈ range (q * a), χ (k : ZMod q) = 0 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show q * (a + 1) = q * a + q by ring, Finset.sum_range_add, ih, zero_add]
    exact sum_range_shift_eq_zero hχ (q * a)

theorem norm_sum_range_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ (k : ZMod q)‖ ≤ q := by
  conv_lhs => rw [← Nat.div_add_mod n q]
  rw [Finset.sum_range_add, sum_range_mul_eq_zero hχ, zero_add]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ range (n % q), ‖χ ((q * (n / q) + i : ℕ) : ZMod q)‖
      ≤ ∑ i ∈ range (n % q), (1 : ℝ) := Finset.sum_le_sum fun i _ => DirichletCharacter.norm_le_one _ _
    _ = (n % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne q))).le

/-- The partial sums `S(n) = Σ_{1 ≤ k ≤ n} χ(k)`. -/
noncomputable def psum (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := ∑ k ∈ Icc 1 n, χ (k : ZMod q)

theorem norm_psum_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (n : ℕ) : ‖psum χ n‖ ≤ q + 1 := by
  have h : ∑ k ∈ range (n + 1), χ (k : ZMod q) = χ (0 : ℕ) + psum χ n := by
    rw [Finset.sum_range_succ', add_comm, psum]
    congr 1
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k : ℕ => χ (k : ZMod q)), zero_add,
      Finset.Ico_add_one_right_eq_Icc]
  have h2 : psum χ n = ∑ k ∈ range (n + 1), χ (k : ZMod q) - χ (0 : ℕ) := by rw [h]; ring
  rw [h2]
  refine (norm_sub_le _ _).trans (add_le_add (norm_sum_range_le hχ _) ?_)
  exact DirichletCharacter.norm_le_one _ _

omit [NeZero q] in
theorem measurable_psum_floor (χ : DirichletCharacter ℂ q) :
    Measurable fun t : ℝ => psum χ ⌊t⌋₊ :=
  (measurable_from_nat (f := psum χ)).comp Nat.measurable_floor

/-! ## `L(s, χ) = s ∫₁^∞ S(t) t^{-s-1} dt` for `ℜs > 0` -/

/-- `∫₁^∞ S(t) t^{-s-1} dt`. -/
noncomputable def Iint (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))

theorem norm_cpow_neg {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]; simp

theorem aesm_integrand (χ : DirichletCharacter ℂ q) (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Ioi 1)) := by
  refine (measurable_psum_floor χ).aestronglyMeasurable.mul ?_
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const t _
    (Or.inr (by have : (1:ℝ) < t := ht; positivity))).continuousWithinAt

theorem integrableOn_integrand {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  refine ((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul
    ((q : ℝ) + 1)).mono' (aesm_integrand χ s) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : (0:ℝ) < t := lt_trans one_pos ht
  rw [norm_mul, norm_cpow_neg ht']
  exact mul_le_mul_of_nonneg_right (norm_psum_le hχ _) (Real.rpow_nonneg ht'.le _)

theorem hasDerivAt_Iint {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s₀ : ℂ} (hs : 0 < s₀.re) :
    HasDerivAt (Iint χ) (∫ t in Ioi (1:ℝ), psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s₀ + 1)) *
      (-(Real.log t : ℂ))) s₀ := by
  set σ₀ := s₀.re
  have hball : ∀ s ∈ Metric.ball s₀ (σ₀ / 2), σ₀ / 2 < s.re := fun s hs' => by
    rw [Metric.mem_ball, dist_eq_norm] at hs'
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le (s.re - s₀.re)]
  have hbd : IntegrableOn (fun t : ℝ => ((q : ℝ) + 1) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun s t => psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)))
    (F' := fun s t => psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)) * (-(Real.log t : ℂ))) (x₀ := s₀)
    (bound := fun t => ((q : ℝ) + 1) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1))
    (Metric.ball_mem_nhds s₀ (half_pos hs))
    (Filter.Eventually.of_forall fun s => aesm_integrand χ s)
    (integrableOn_integrand hχ hs)
    ((aesm_integrand χ s₀).mul
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
      calc ‖psum χ ⌊t⌋₊‖ * t ^ (-(s.re + 1)) * Real.log t
          ≤ ((q : ℝ) + 1) * t ^ (-(σ₀ / 2) - 1) * (t ^ (σ₀ / 4) / (σ₀ / 4)) :=
            mul_le_mul (mul_le_mul (norm_psum_le hχ _) hpow (Real.rpow_nonneg ht0.le _)
              (by positivity)) hlog (Real.log_nonneg ht'.le) (by positivity)
          _ = ((q : ℝ) + 1) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1) := by rw [mul_assoc, e]; ring))
    hbd
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht s _ => by
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht
      have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have h1 : HasDerivAt (fun s : ℂ => -(s + 1)) (-1) s := ((hasDerivAt_id s).add_const 1).neg
      refine ((h1.const_cpow (Or.inl ht0')).const_mul (psum χ ⌊t⌋₊)).congr_deriv ?_
      rw [← Complex.ofReal_log ht0.le]; ring))
  exact h.2

theorem differentiableOn_mul_Iint {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (fun s => s * Iint χ s) {s : ℂ | 0 < s.re} := fun s hs =>
  (differentiableAt_id.mul (hasDerivAt_Iint hχ hs).differentiableAt).differentiableWithinAt

theorem LFunction_eq_mul_Iint {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s = s * Iint χ s := by
  set U := {s : ℂ | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ χ.LFunction U := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hg : AnalyticOnNhd ℂ (fun s => s * Iint χ s) U :=
    (differentiableOn_mul_Iint hχ).analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ U := by show (0:ℝ) < (2:ℂ).re; norm_num
  have hev : χ.LFunction =ᶠ[nhds (2 : ℂ)] fun s => s * Iint χ s := by
    have hopen : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show (1:ℝ) < (2:ℂ).re; norm_num)
    filter_upwards [hopen] with s hs1
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
    have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
      refine Asymptotics.IsBigO.of_bound ((q : ℝ) + 1) (Filter.Eventually.of_forall fun n => ?_)
      simp only [Real.rpow_zero, norm_one, mul_one]
      exact norm_psum_le hχ n
    exact LSeries_eq_mul_integral _ le_rfl (by linarith) (χ.LSeriesSummable_of_one_lt_re hs1) hO
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2 hev hs

/-- **`|L(s, χ)| ≤ (q + 1)|s|/ℜs`** for `ℜs > 0`, `χ ≠ 1`. -/
theorem norm_LFunction_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ ((q : ℝ) + 1) * ‖s‖ / s.re := by
  rw [LFunction_eq_mul_Iint hχ hs, norm_mul, Iint]
  have hb : ‖∫ t in Ioi (1:ℝ), psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))‖ ≤ ((q : ℝ) + 1) / s.re := by
    have hi := (integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul
      ((q : ℝ) + 1)
    refine (norm_integral_le_of_norm_le hi ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
    · have ht' : (0:ℝ) < t := lt_trans one_pos ht
      rw [norm_mul, norm_cpow_neg ht']
      exact mul_le_mul_of_nonneg_right (norm_psum_le hχ _) (Real.rpow_nonneg ht'.le _)
    · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
      have : s.re ≠ 0 := hs.ne'
      field_simp
      ring_nf
      field_simp
  calc ‖s‖ * ‖∫ t in Ioi (1:ℝ), psum χ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (((q : ℝ) + 1) / s.re) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

end TernaryGoldbach.Explicit
