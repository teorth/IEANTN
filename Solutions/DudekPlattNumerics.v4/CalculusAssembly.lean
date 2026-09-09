/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors (AI-assisted)
-/
import IntegralBounds

/-!
# Analytic assembly from scalar certificates

Every numeric input below is an explicit local hypothesis. These are NOT new
asserted graph inputs. Integration must discharge them with the peer numeric
proofs. The prime-counting identities and all integral transports used here are
proved in ThetaPi and IntegralBounds, not hypotheses.
-/

namespace DudekPlattNumerics.Calculus
open Real MeasureTheory Set

lemma A_nonneg : 0 ≤ A := by
  have : 0 < log (2 : ℝ) := log_pos (by norm_num)
  unfold A
  positivity

lemma normalize_error_majorant {L K : ℝ} (hL : 0 < L) :
    L ^ 6 / exp L * (4 * exp ((99 / 100 : ℝ) * L) +
      K * exp L / log (exp ((99 / 100 : ℝ) * L)) ^ 7) =
      4 * L ^ 6 * exp (-L / 100) + K / ((99 / 100 : ℝ) ^ 7 * L) := by
  have hL0 := ne_of_gt hL
  have he0 := ne_of_gt (exp_pos L)
  have hr : exp ((99 / 100 : ℝ) * L) / exp L = exp (-L / 100) := by
    rw [← exp_sub]
    congr 1
    ring
  rw [log_exp]
  calc
    _ = 4 * L ^ 6 * (exp ((99 / 100 : ℝ) * L) / exp L) +
        K / ((99 / 100 : ℝ) ^ 7 * L) := by field_simp
    _ = _ := by rw [hr]

lemma normalize_I7_majorant {L : ℝ} (hL : 0 < L) :
    L ^ 6 / exp L * (720 * (exp L / log (exp L) ^ 7 +
      7 * (sqrt (exp L) / log 2 ^ 8 + 256 * exp L / log (exp L) ^ 8))) =
      720 * (1 / L + 7 * (L ^ 6 * exp (-L / 2) / log 2 ^ 8 + 256 / L ^ 2)) := by
  have hL0 := ne_of_gt hL
  have he0 := ne_of_gt (exp_pos L)
  have hl0 : log (2 : ℝ) ≠ 0 := ne_of_gt (log_pos (by norm_num))
  have hr : exp (L / 2) / exp L = exp (-L / 2) := by
    rw [← exp_sub]
    congr 1
    ring
  rw [log_exp, ← exp_half]
  calc
    _ = 720 * (1 / L + 7 * (L ^ 6 * (exp (L / 2) / exp L) /
        log 2 ^ 8 + 256 / L ^ 2)) := by field_simp
    _ = _ := by rw [hr]

lemma normalized_errorIntegral_lt (hlog2 : (2 / 3 : ℝ) < log 2)
    {L K : ℝ} (hL : 9400 ≤ L) (hK : 0 ≤ K)
    (htail : ∀ t : ℝ, exp ((99 / 100 : ℝ) * L) ≤ t →
      |thetaError t| ≤ K * t / log t ^ 5)
    (hD : 4 * L ^ 6 * exp (-L / 100) + K / ((99 / 100 : ℝ) ^ 7 * L) < 1 / 2) :
    L ^ 6 / exp L * |errorIntegral (exp L)| < 1 / 2 := by
  have hLpos : 0 < L := by linarith
  have hs : 2 ≤ exp ((99 / 100 : ℝ) * L) := by
    linarith [add_one_le_exp ((99 / 100 : ℝ) * L)]
  have hsx : exp ((99 / 100 : ℝ) * L) ≤ exp L := by
    apply exp_le_exp.mpr
    linarith
  have hb := errorIntegral_split_bound hlog2 hs hsx hK (fun t ht ↦ htail t ht.1)
  have hscale : 0 ≤ L ^ 6 / exp L := by positivity
  calc
    _ ≤ L ^ 6 / exp L * (4 * exp ((99 / 100 : ℝ) * L) +
        K * exp L / log (exp ((99 / 100 : ℝ) * L)) ^ 7) :=
      mul_le_mul_of_nonneg_left hb hscale
    _ = _ := normalize_error_majorant hLpos
    _ < _ := hD

lemma normalized_I7_lt {L : ℝ} (hL : 9400 ≤ L)
    (hI7 : 720 * (1 / L + 7 * (L ^ 6 * exp (-L / 2) / log 2 ^ 8 + 256 / L ^ 2)) <
      1 / 10) :
    L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) < 1 / 10 := by
  have hLpos : 0 < L := by linarith
  have hx : 4 ≤ exp L := by linarith [add_one_le_exp L]
  have hb := I7_bound hx
  calc
    _ ≤ L ^ 6 / exp L * (720 * (exp L / log (exp L) ^ 7 +
        7 * (sqrt (exp L) / log 2 ^ 8 + 256 * exp L / log (exp L) ^ 8))) := by
      gcongr
    _ = _ := normalize_I7_majorant hLpos
    _ < _ := hI7

/-- All analytic work is discharged; the explicitly listed scalar certificates
and theta bounds are the isolated-stage numeric interface, not axioms. -/
theorem coefficients_from_logarithmic_certificates
    (hlog2 : (2 / 3 : ℝ) < log 2) {L K : ℝ} (hL : 9400 ≤ L) (hK : 0 ≤ K)
    (hpoint : |thetaError (exp L)| ≤ 3110 * exp L / L ^ 5)
    (htail : ∀ t : ℝ, exp ((99 / 100 : ℝ) * L) ≤ t →
      |thetaError t| ≤ K * t / log t ^ 5)
    (hD : 4 * L ^ 6 * exp (-L / 100) + K / ((99 / 100 : ℝ) ^ 7 * L) < 1 / 2)
    (hI7 : 720 * (1 / L + 7 * (L ^ 6 * exp (-L / 2) / log 2 ^ 8 + 256 / L ^ 2)) <
      1 / 10)
    (hA : 2 * A * L ^ 6 * exp (-L) < 1 / 1000) :
    -2990.501 < L ^ 6 / exp L * (IEANTN.primeCounting (exp L) - S5 (exp L)) ∧
      L ^ 6 / exp L * (IEANTN.primeCounting (exp L) - S5 (exp L)) < 3230.6 := by
  have hLpos : 0 < L := by linarith
  have hL0 := ne_of_gt hLpos
  have he0 := ne_of_gt (exp_pos L)
  have hx : 2 ≤ exp L := by linarith [add_one_le_exp L]
  have hq : 0 < L ^ 6 / exp L := by positivity
  have hp : |L ^ 6 / exp L * (thetaError (exp L) / L)| ≤ 3110 := by
    rw [abs_mul, abs_of_pos hq, abs_div, abs_of_pos hLpos]
    calc
      _ ≤ L ^ 6 / exp L * ((3110 * exp L / L ^ 5) / L) := by gcongr
      _ = _ := by field_simp
  have he : |L ^ 6 / exp L * errorIntegral (exp L)| < 1 / 2 := by
    rw [abs_mul, abs_of_pos hq]
    exact normalized_errorIntegral_lt hlog2 hL hK htail hD
  have hi := normalized_I7_lt hL hI7
  have hi0 : 0 ≤ L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) (logIntegral_nonneg 7 hx))
  have ha : L ^ 6 / exp L * (2 * A) < 1 / 1000 := by
    convert hA using 1
    rw [exp_neg]
    ring
  have ha0 : 0 ≤ L ^ 6 / exp L * (2 * A) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) A_nonneg)
  have hn : L ^ 6 / exp L * (IEANTN.primeCounting (exp L) - S5 (exp L)) =
      120 + L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) -
        L ^ 6 / exp L * (2 * A) + L ^ 6 / exp L * (thetaError (exp L) / L) +
        L ^ 6 / exp L * errorIntegral (exp L) := by
    rw [primeCounting_expansion hx, log_exp]
    field_simp
    ring
  rw [hn]
  rcases abs_le.mp hp with ⟨hp1, hp2⟩
  rcases abs_lt.mp he with ⟨he1, he2⟩
  constructor <;> linarith

/-- Denormalization gives the published weaker coefficients without modifying
the existing main term, constants, or strict endpoints. -/
theorem weaker_bounds_of_coefficients {x : ℝ} (hx : 1 < x)
    (h : -2990.501 < log x ^ 6 / x * (IEANTN.primeCounting x - S5 x) ∧
      log x ^ 6 / x * (IEANTN.primeCounting x - S5 x) < 3230.6) :
    S5 x - 3010.333 * (x / log x ^ 6) < IEANTN.primeCounting x ∧
      IEANTN.primeCounting x < S5 x + 3250.488 * (x / log x ^ 6) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos hx
  have hq : 0 < log x ^ 6 / x := by positivity
  have hq0 : log x ^ 6 / x ≠ 0 := ne_of_gt hq
  have hh : (log x ^ 6 / x) * (x / log x ^ 6) = 1 := by field_simp
  constructor
  · apply (mul_lt_mul_iff_right₀ hq).mp
    nlinarith [h.1]
  · apply (mul_lt_mul_iff_right₀ hq).mp
    nlinarith [h.2]

/-- Real-x consumer of the proved analytic interface, with the literal strict
threshold used by the numerical node. No floor/logarithm transport remains for
the integration owner. The scalar hypotheses still require numeric proofs. -/
theorem pi_two_sided_from_certificates
    (hlog2 : (2 / 3 : ℝ) < log 2) {x K : ℝ} (hx : exp 9400 < x) (hK : 0 ≤ K)
    (hpoint : |thetaError x| ≤ 3110 * x / log x ^ 5)
    (htail : ∀ t : ℝ, exp ((99 / 100 : ℝ) * log x) ≤ t →
      |thetaError t| ≤ K * t / log t ^ 5)
    (hD : 4 * log x ^ 6 * exp (-log x / 100) +
      K / ((99 / 100 : ℝ) ^ 7 * log x) < 1 / 2)
    (hI7 : 720 * (1 / log x + 7 *
      (log x ^ 6 * exp (-log x / 2) / log 2 ^ 8 + 256 / log x ^ 2)) < 1 / 10)
    (hA : 2 * A * log x ^ 6 * exp (-log x) < 1 / 1000) :
    S5 x - 3010.333 * (x / log x ^ 6) < IEANTN.primeCounting x ∧
      IEANTN.primeCounting x < S5 x + 3250.488 * (x / log x ^ 6) := by
  have hx0 : 0 < x := lt_trans (exp_pos _) hx
  have hx1 : 1 < x := by linarith [add_one_le_exp (9400 : ℝ)]
  have hL : 9400 ≤ log x := by
    have := log_lt_log (exp_pos _) hx
    simpa only [log_exp] using this.le
  apply weaker_bounds_of_coefficients hx1
  have hc := coefficients_from_logarithmic_certificates hlog2 hL hK
    (by simpa only [exp_log hx0] using hpoint) htail hD hI7 hA
  simpa only [exp_log hx0] using hc

end DudekPlattNumerics.Calculus
