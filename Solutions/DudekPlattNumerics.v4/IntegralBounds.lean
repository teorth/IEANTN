/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastián Rodrigo (AI-assisted)
-/
import ThetaPi

/-!
# Whole-range integral bounds

Elementary estimates are proved for the native theta function, without using the
literature estimate below its domain. Scalar endpoint certificates are separated
from these calculus lemmas and are explicit parameters where needed.
-/

namespace DudekPlattNumerics.Calculus
open Real MeasureTheory Set

lemma primeCounting_le_self {x : ℝ} (hx : 0 ≤ x) : IEANTN.primeCounting x ≤ x := by
  have hn (n : ℕ) : Nat.primeCounting n ≤ n := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Ioc_zero]
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  unfold IEANTN.primeCounting
  exact le_trans (by exact_mod_cast hn ⌊x⌋₊) (Nat.floor_le hx)

/-- The original elementary bound works right down to 2. -/
theorem theta_le_self_mul_log {t : ℝ} (ht : 2 ≤ t) :
    Chebyshev.theta t ≤ t * log t := by
  exact (Chebyshev.theta_le_pi_mul_log' t).trans
    (mul_le_mul_of_nonneg_right (primeCounting_le_self (by linarith))
      (log_nonneg (by linarith)))

/-- No theta estimate from the literature is used on the early interval. -/
theorem abs_errorKernel_le_four (hlog2 : (2 / 3 : ℝ) < log 2)
    {t : ℝ} (ht : 2 ≤ t) : |thetaError t / (t * log t ^ 2)| ≤ 4 := by
  have ht0 : 0 < t := by linarith
  have hl : (2 / 3 : ℝ) < log t :=
    lt_of_lt_of_le hlog2 (log_le_log (by norm_num) ht)
  have hl0 : 0 < log t := by linarith
  have he : |thetaError t| ≤ t * log t + t := by
    rw [thetaError]
    calc
      |Chebyshev.theta t - t| ≤ |Chebyshev.theta t| + |t| := abs_sub _ _
      _ ≤ t * log t + t := by
        rw [abs_of_nonneg (Chebyshev.theta_nonneg t), abs_of_pos ht0]
        exact add_le_add (theta_le_self_mul_log ht) le_rfl
  rw [abs_div, abs_of_pos (mul_pos ht0 (pow_pos hl0 2))]
  apply (div_le_iff₀ (mul_pos ht0 (pow_pos hl0 2))).mpr
  have hb : log t + 1 ≤ 4 * log t ^ 2 := by
    nlinarith [sq_nonneg (log t - 2 / 3)]
  nlinarith [mul_le_mul_of_nonneg_left hb ht0.le]

lemma integral_logKernel_le (k : ℕ) {a b : ℝ} (hab : a ≤ b) (ha : 1 < a) :
    (∫ t in a..b, 1 / log t ^ k) ≤ (b - a) / log a ^ k := by
  calc
    _ ≤ ∫ t in a..b, 1 / log a ^ k := by
      refine intervalIntegral.integral_mono_on hab
        (intervalIntegrable_logKernel k ha (lt_of_lt_of_le ha hab))
        (by simp) ?_
      intro t ht
      have hlog : 0 < log a := log_pos ha
      have hlogs : log a ≤ log t := log_le_log (by linarith) ht.1
      gcongr
    _ = _ := by simp [div_eq_mul_inv]

lemma logIntegral_nonneg (k : ℕ) {x : ℝ} (hx : 2 ≤ x) : 0 ≤ logIntegral k x := by
  apply intervalIntegral.integral_nonneg hx
  intro t ht
  have : 0 ≤ log t := log_nonneg (by linarith [ht.1])
  positivity

lemma logIntegral_pos (k : ℕ) {x : ℝ} (hx : 2 < x) : 0 < logIntegral k x := by
  apply intervalIntegral.integral_pos hx
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ^ k ≠ 0 := pow_ne_zero _
      (ne_of_gt (log_pos (by linarith [ht.1])))
    apply ContinuousAt.continuousWithinAt
    fun_prop
  · intro t ht
    have : 0 ≤ log t := log_nonneg (by linarith [ht.1])
    positivity
  · refine ⟨2, ⟨le_rfl, hx.le⟩, ?_⟩
    have : 0 < log (2 : ℝ) := log_pos (by norm_num)
    positivity

/-- A split at sqrt(x), valid on both entire subintervals. -/
theorem logIntegral_sqrt_bound (k : ℕ) {x : ℝ} (hx : 4 ≤ x) :
    logIntegral k x ≤ sqrt x / log 2 ^ k + 2 ^ k * x / log x ^ k := by
  have hs : 2 ≤ sqrt x := le_sqrt_of_sq_le (by norm_num; exact hx)
  have hsx : sqrt x ≤ x := (sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  unfold logIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := sqrt x)
    (intervalIntegrable_logKernel k (by norm_num) (by linarith))
    (intervalIntegrable_logKernel k (by linarith) (by linarith))]
  calc
    _ ≤ (sqrt x - 2) / log 2 ^ k + (x - sqrt x) / log (sqrt x) ^ k :=
      add_le_add (integral_logKernel_le k hs (by norm_num))
        (integral_logKernel_le k hsx (by linarith))
    _ ≤ sqrt x / log 2 ^ k + x / log (sqrt x) ^ k := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hlog2.le k)
      · exact div_le_div_of_nonneg_right (by linarith [sqrt_nonneg x])
          (pow_nonneg (log_nonneg (by linarith)) k)
    _ = _ := by rw [log_sqrt hx0.le, div_pow, div_div_eq_mul_div]; ring

/-- The I7 majorant used by the corrected derivation; the lower-end correction
is discarded in the safe direction, rather than silently omitted. -/
theorem I7_bound {x : ℝ} (hx : 4 ≤ x) :
    logIntegral 7 x ≤ x / log x ^ 7 +
      7 * (sqrt x / log 2 ^ 8 + 256 * x / log x ^ 8) := by
  have hr := logIntegral_recurrence 6 (by linarith : 2 ≤ x)
  have hi := logIntegral_sqrt_bound 8 hx
  norm_num at hr hi
  have hpos : 0 ≤ 2 / log (2 : ℝ) ^ 7 := by positivity
  linarith

/-- Native pointwise theta bounds transport to the logarithmic integrand.
The hypotheses here will be discharged by the numeric theta-error module. -/
theorem abs_errorKernel_le_tail {s t K : ℝ} (hs : 2 ≤ s) (hst : s ≤ t)
    (hK : 0 ≤ K) (he : |thetaError t| ≤ K * t / log t ^ 5) :
    |thetaError t / (t * log t ^ 2)| ≤ K / log s ^ 7 := by
  have ht0 : 0 < t := by linarith
  have hslog : 0 < log s := log_pos (by linarith)
  have htlog : 0 < log t := log_pos (by linarith)
  have hl : log s ≤ log t := log_le_log (by linarith) hst
  rw [abs_div, abs_of_pos (mul_pos ht0 (pow_pos htlog 2))]
  calc
    _ ≤ (K * t / log t ^ 5) / (t * log t ^ 2) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ = K / log t ^ 7 := by field_simp
    _ ≤ K / log s ^ 7 := by gcongr

/-- Bound the entire error integral, including the elementary early interval.
No estimate valid only at large t is applied below the split s. -/
theorem errorIntegral_split_bound (hlog2 : (2 / 3 : ℝ) < log 2)
    {x s K : ℝ} (hs : 2 ≤ s) (hsx : s ≤ x) (hK : 0 ≤ K)
    (he : ∀ t ∈ Icc s x, |thetaError t| ≤ K * t / log t ^ 5) :
    |errorIntegral x| ≤ 4 * s + K * x / log s ^ 7 := by
  have hx : 2 ≤ x := hs.trans hsx
  have hi1 := intervalIntegrable_errorKernel (le_refl 2) hs
  have hi2 := intervalIntegrable_errorKernel hs hx
  have h1 : |∫ t in (2 : ℝ)..s, thetaError t / (t * log t ^ 2)| ≤ 4 * (s - 2) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (2 : ℝ)) (b := s) (C := (4 : ℝ))
      (f := fun t ↦ thetaError t / (t * log t ^ 2)) (fun t ht ↦ by
        rw [Set.uIoc_of_le hs] at ht
        simpa only [Real.norm_eq_abs] using abs_errorKernel_le_four hlog2 ht.1.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs)] using hb
  have h2 : |∫ t in s..x, thetaError t / (t * log t ^ 2)| ≤
      (K / log s ^ 7) * (x - s) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := x) (C := K / log s ^ 7)
      (f := fun t ↦ thetaError t / (t * log t ^ 2)) (fun t ht ↦ by
        rw [Set.uIoc_of_le hsx] at ht
        simpa only [Real.norm_eq_abs] using
          abs_errorKernel_le_tail hs ht.1.le hK (he t ⟨ht.1.le, ht.2⟩))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsx)] using hb
  unfold errorIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  calc
    _ ≤ |∫ t in (2 : ℝ)..s, thetaError t / (t * log t ^ 2)| +
        |∫ t in s..x, thetaError t / (t * log t ^ 2)| := abs_add_le _ _
    _ ≤ 4 * (s - 2) + (K / log s ^ 7) * (x - s) := add_le_add h1 h2
    _ ≤ 4 * s + K * x / log s ^ 7 := by
      have hpos : 0 ≤ K / log s ^ 7 := by
        have : 0 < log s := log_pos (by linarith)
        positivity
      calc
        _ ≤ 4 * s + (K / log s ^ 7) * x := by
          nlinarith [mul_nonneg hpos (show 0 ≤ s by linarith)]
        _ = _ := by ring

end DudekPlattNumerics.Calculus
