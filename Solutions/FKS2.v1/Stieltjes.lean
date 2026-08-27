/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Integral

/-!
# Partial summation: `π − Li` in terms of `θ`

The paper's (Stieltjes), and the decomposition of `Eπ` that Theorem 3 estimates term by term.

`Mathlib` supplies the harder half — `Chebyshev.primeCounting_eq_theta_div_log_add_integral` is
Abel summation for `π` against `θ`. What is added here is the matching identity for the logarithmic
integral,

`Li(x) = x/log x − 2/log 2 + ∫₂ˣ dt/log²t`,

which is one integration by parts, and then the subtraction that makes the two `∫ dt/log²t` terms
cancel into a single `∫ (θ(t) − t)/(t log²t)`. That is exactly the integral `Integral.lean` bounds.

## What comes out

`piMinusLi_eq` is the identity based at `2`; `piMinusLi_sub` rebases it at any `x₀ ≥ 2`, which is
the form the paper uses so that `π(x₀)` and `θ(x₀)` can be computed numerically. `Epi_le` then
divides through by `x/log x` and applies the triangle inequality, leaving the three terms Theorem 3
bounds separately: a boundary constant, `Eθ(x)` itself, and the integral.
-/

namespace FKS2Sol

open Real IEANTN intervalIntegral MeasureTheory

theorem continuousOn_inv_log {x : ℝ} (hx : 2 ≤ x) (n : ℕ) :
    ContinuousOn (fun t : ℝ => 1 / (log t) ^ n) (Set.uIcc 2 x) := by
  rw [Set.uIcc_of_le hx]
  intro t ht
  have ht1 : (1 : ℝ) < t := by linarith [ht.1]
  have hlog : 0 < log t := log_pos ht1
  have hne : (log t) ^ n ≠ 0 := pow_ne_zero _ hlog.ne'
  exact ((continuousAt_const.div ((continuousAt_log (by linarith)).pow n) hne)).continuousWithinAt

/-- `Li(x) = x/log x - 2/log 2 + ∫₂ˣ dt/log²t`, by parts. -/
theorem Li_eq {x : ℝ} (hx : 2 ≤ x) :
    Li x = x / log x - 2 / log 2 + ∫ t in (2 : ℝ)..x, 1 / (log t) ^ 2 := by
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / (log t) ^ 1) volume 2 x :=
    (continuousOn_inv_log hx 1).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / (log t) ^ 2) volume 2 x :=
    (continuousOn_inv_log hx 2).intervalIntegrable
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun s : ℝ => s / log s) (1 / (log t) ^ 1 - 1 / (log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have hlog : 0 < log t := log_pos (by linarith [ht.1])
    have hL : HasDerivAt log (1 / t) t := by simpa using Real.hasDerivAt_log htpos.ne'
    have hne : log t ≠ 0 := hlog.ne'
    have htne : t ≠ 0 := htpos.ne'
    have h := (hasDerivAt_id t).div hL hne
    refine h.congr_deriv ?_
    simp only [id_eq]
    field_simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
  have hsplit := intervalIntegral.integral_sub hint1 hint2
  unfold Li
  simp only [pow_one] at hFTC hsplit hint1 ⊢
  linarith [hFTC, hsplit]


theorem contOn_inv_t_log_sq {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    ContinuousOn (fun t : ℝ => (t * (log t) ^ 2)⁻¹) (Set.uIcc x₀ x) := by
  rw [Set.uIcc_of_le hx]
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le hx₀ ht.1
  have hlog : 0 < log t := log_pos ht1
  have hne : t * (log t) ^ 2 ≠ 0 := by positivity
  exact ((continuousAt_id.mul
    ((continuousAt_log (by linarith)).pow 2)).inv₀ hne).continuousWithinAt

theorem intervalIntegrable_theta_div {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * (log t) ^ 2)) volume x₀ x := by
  simpa [div_eq_mul_inv] using
    Chebyshev.theta_mono.intervalIntegrable.mul_continuousOn (contOn_inv_t_log_sq hx₀ hx)

theorem intervalIntegrable_sub_div {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.theta t - t) / (t * (log t) ^ 2)) volume x₀ x := by
  have h := (Chebyshev.theta_mono.intervalIntegrable.sub
    (continuous_id.intervalIntegrable (μ := volume) x₀ x)).mul_continuousOn (contOn_inv_t_log_sq hx₀ hx)
  simpa [div_eq_mul_inv] using h

/-- **The Stieltjes identity**: `π(x) − Li(x)` in terms of `θ`. -/
theorem piMinusLi_eq {x : ℝ} (hx : 2 ≤ x) :
    primeCounting x - Li x
      = (Chebyshev.theta x - x) / log x + 2 / log 2
        + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2) := by
  have hpi := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hli := Li_eq hx
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / (log t) ^ 2) volume 2 x :=
    (continuousOn_inv_log hx 2).intervalIntegrable
  have hcongr : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2))
      = (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (log t) ^ 2))
        - ∫ t in (2 : ℝ)..x, 1 / (log t) ^ 2 := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_theta_div one_lt_two hx) hint2]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have htne : t ≠ 0 := by linarith [ht.1]
    have hlog : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    field_simp
  unfold primeCounting Li
  rw [hcongr, sub_div]
  unfold Li at hli
  rw [hpi]
  linarith [hli]


/-- The Stieltjes identity relative to a base point `x₀`, the paper's displayed rewrite. -/
theorem piMinusLi_sub {x₀ x : ℝ} (hx₀ : 2 ≤ x₀) (hx : x₀ ≤ x) :
    primeCounting x - Li x
      = (primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀)
        + (Chebyshev.theta x - x) / log x
        + ∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2) := by
  have hx2 : (2 : ℝ) ≤ x := le_trans hx₀ hx
  have h1 := piMinusLi_eq hx2
  have h2 := piMinusLi_eq hx₀
  have hsplit := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_sub_div one_lt_two hx2) (intervalIntegrable_sub_div one_lt_two hx₀)
  linarith

/-- `Eπ` bounded by a boundary term, `Eθ`, and the integral — the paper's
(starting_bound_on_pi) after normalising by `x / log x`. -/
theorem Epi_le {x₀ x : ℝ} (hx₀ : 2 ≤ x₀) (hx : x₀ ≤ x) :
    Eπ x ≤ (log x / x) * |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀|
      + Eθ x
      + (log x / x) * |∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)| := by
  have hx2 : (2 : ℝ) ≤ x := le_trans hx₀ hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have htri : |primeCounting x - Li x|
      ≤ |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀|
        + |Chebyshev.theta x - x| / log x
        + |∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)| := by
    rw [piMinusLi_sub hx₀ hx]
    have h1 := abs_add_le (primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀
        + (Chebyshev.theta x - x) / log x)
      (∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2))
    have h2 := abs_add_le (primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀)
      ((Chebyshev.theta x - x) / log x)
    have h3 : |(Chebyshev.theta x - x) / log x| = |Chebyshev.theta x - x| / log x := by
      rw [abs_div, abs_of_pos hlog]
    linarith
  have hmul : (0 : ℝ) < log x / x := by positivity
  have hscaled := mul_le_mul_of_nonneg_right htri hmul.le
  have hexp : (|primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀|
      + |Chebyshev.theta x - x| / log x
      + |∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)|) * (log x / x)
      = (log x / x) * |primeCounting x₀ - Li x₀ - (Chebyshev.theta x₀ - x₀) / log x₀|
        + |Chebyshev.theta x - x| / x
        + (log x / x) * |∫ t in x₀..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)| := by
    field_simp
  unfold Eπ Eθ
  have hkey : |primeCounting x - Li x| / (x / log x)
      = |primeCounting x - Li x| * (log x / x) := by field_simp
  rw [hkey]
  linarith [hscaled, hexp]

end FKS2Sol
