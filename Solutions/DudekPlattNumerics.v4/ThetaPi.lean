/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastián Rodrigo (AI-assisted)
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Native theta-to-pi partial summation and finite integration by parts

These are helper theorems, not graph inputs. The first identity uses Mathlib's
Abel summation theorem for the actual prime counting function (including jumps
and natural-floor endpoint conventions). No hypothesis about primes is used.
-/

namespace DudekPlattNumerics.Calculus

open Real MeasureTheory Set

noncomputable def thetaError (t : ℝ) : ℝ := Chebyshev.theta t - t
noncomputable def logIntegral (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ k
noncomputable def errorIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, thetaError t / (t * Real.log t ^ 2)
noncomputable def S5 (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 5, (Nat.factorial k : ℝ) / Real.log x ^ (k + 1)
noncomputable def A : ℝ :=
  1 / log 2 ^ 2 + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 +
    24 / log 2 ^ 5 + 120 / log 2 ^ 6

/-- The expanded lower-end constant is exactly the factorial sum in the paper. -/
lemma A_eq_sum : A = ∑ k ∈ Finset.range 5,
    (Nat.factorial (k + 1) : ℝ) / log 2 ^ (k + 2) := by
  norm_num [A, Finset.sum_range_succ, Nat.factorial]

lemma intervalIntegrable_logKernel (k : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ 1 / log t ^ k) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at ht
  have ht1 : 1 < t := by rcases ht with ht | ht <;> linarith [ht.1, ht.2]
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl : log t ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt (log_pos ht1))
  fun_prop

lemma intervalIntegrable_thetaKernel {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ Chebyshev.theta t / (t * log t ^ 2)) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply (Chebyshev.integrableOn_theta_div_id_mul_log_sq (max a b)).mono_set
  intro t ht
  exact ⟨le_trans (le_min ha hb) ht.1.le, ht.2⟩

lemma intervalIntegrable_errorKernel {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ thetaError t / (t * log t ^ 2)) volume a b := by
  have hi := (intervalIntegrable_thetaKernel ha hb).sub
    (intervalIntegrable_logKernel 2 (by linarith : 1 < a) (by linarith : 1 < b))
  apply hi.congr
  intro t ht
  have ht0 : t ≠ 0 := by
    have := lt_of_le_of_lt (le_min ha hb) ht.1
    linarith
  dsimp [thetaError]
  field_simp

/-- Native Abel summation after separating the elementary part of theta. -/
theorem primeCounting_eq_error {x : ℝ} (hx : 2 ≤ x) :
    IEANTN.primeCounting x = x / log x + logIntegral 2 x +
      thetaError x / log x + errorIntegral x := by
  have hs := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hi := intervalIntegral.integral_sub
    (intervalIntegrable_thetaKernel (le_refl 2) hx)
    (intervalIntegrable_logKernel 2 (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x))
  have he : errorIntegral x =
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) - logIntegral 2 x := by
    rw [errorIntegral, logIntegral, ← hi]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
    dsimp [thetaError]
    field_simp
  dsimp [IEANTN.primeCounting]
  rw [he, hs]
  dsimp [thetaError]
  ring

lemma hasDerivAt_div_log_pow (k : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ t / log t ^ (k + 1))
      (1 / log t ^ (k + 1) - (k + 1 : ℝ) / log t ^ (k + 2)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl : log t ≠ 0 := ne_of_gt (log_pos ht)
  convert! (hasDerivAt_id t).div ((hasDerivAt_log ht0).pow (k + 1))
    (pow_ne_zero _ hl) using 1
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, pow_zero, one_mul]
  field_simp

/-- Integration by parts with the actual lower endpoint 2. -/
theorem logIntegral_recurrence (k : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    logIntegral (k + 1) x = x / log x ^ (k + 1) - 2 / log 2 ^ (k + 1) +
      (k + 1 : ℝ) * logIntegral (k + 2) x := by
  have h1 : 1 < x := by linarith
  have hi1 := intervalIntegrable_logKernel (k + 1) (by norm_num : (1 : ℝ) < 2) h1
  have hi2 := (intervalIntegrable_logKernel (k + 2)
    (by norm_num : (1 : ℝ) < 2) h1).const_mul (k + 1 : ℝ)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (2 : ℝ)) (b := x)
    (f := fun t : ℝ ↦ t / log t ^ (k + 1))
    (f' := fun t : ℝ ↦ 1 / log t ^ (k + 1) - (k + 1 : ℝ) / log t ^ (k + 2))
    (fun t ht ↦ hasDerivAt_div_log_pow k (by
      rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]))
    (by simpa only [div_eq_mul_inv, one_mul] using hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 (by
    simpa only [div_eq_mul_inv, one_mul] using hi2)] at hf
  simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul] at hf
  dsimp [logIntegral]
  simp only [div_eq_mul_inv, one_mul] at hf ⊢
  linarith

/-- Five finite integrations by parts. There is no primewise differentiation. -/
theorem mainTerm_identity {x : ℝ} (hx : 2 ≤ x) :
    x / log x + logIntegral 2 x =
      S5 x + 120 * x / log x ^ 6 + 720 * logIntegral 7 x - 2 * A := by
  have h2 := logIntegral_recurrence 1 hx
  have h3 := logIntegral_recurrence 2 hx
  have h4 := logIntegral_recurrence 3 hx
  have h5 := logIntegral_recurrence 4 hx
  have h6 := logIntegral_recurrence 5 hx
  norm_num at h2 h3 h4 h5 h6
  rw [h2, h3, h4, h5, h6]
  dsimp [S5, A]
  norm_num [Finset.sum_range_succ, Nat.factorial]
  ring

/-- Exact identity required for the Dudek--Platt numerical derivation. -/
theorem primeCounting_expansion {x : ℝ} (hx : 2 ≤ x) :
    IEANTN.primeCounting x = S5 x + 120 * x / log x ^ 6 +
      720 * logIntegral 7 x - 2 * A + thetaError x / log x + errorIntegral x := by
  rw [primeCounting_eq_error hx, mainTerm_identity hx]

end DudekPlattNumerics.Calculus
