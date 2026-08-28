/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.FKS2.v1.Conclusions
import IEANTN.Nodes.FKS2.v2.Conclusions
import IEANTN.Nodes.FKS.v1.Conclusions
import IEANTN.Nodes.BKLNW.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Shared support for `FKS2.v1`'s corollaries

Small facts the corollaries need. The analysis proper — Lemma 10, Lemma 12, the Stieltjes identity,
and the two conversions — lives in `Solutions/FKS2.v2`, because the conclusions it proves now live
on `FKS2.v2`. This solution takes those two pipelines as **hypotheses**, which is what the corollaries
importing them means.
-/

namespace FKS2Sol

open Real IEANTN intervalIntegral MeasureTheory
open FKS2.v2 (nuAsymp)

/-- The admissible bound is monotone in `A`, the only place `A` appears being a positive factor. -/
theorem admissibleBound_mono_A {A A' B C R x : ℝ} (hR : 0 < R) (hx : 1 < x) (h : A ≤ A') :
    admissibleBound A B C R x ≤ admissibleBound A' B C R x := by
  have hlog : 0 < log x := log_pos hx
  unfold admissibleBound
  gcongr

/-- `1 ≤ log 10`, needed only to place `b = 30` inside `BKLNW`'s range `7 ≤ b ≤ 38 log 10`. -/
theorem one_le_log_ten : (1 : ℝ) ≤ log 10 := by
  rw [show (1 : ℝ) = log (exp 1) from (log_exp 1).symm]
  exact log_le_log (exp_pos 1) (by nlinarith [Real.exp_one_lt_three])

theorem BKLNW_f_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ BKLNW.v1.f x :=
  Finset.sum_nonneg fun _ _ ↦ rpow_nonneg hx _

theorem BKLNW_a₂_nonneg {b : ℝ} : 0 ≤ BKLNW.v1.a₂ b := by
  unfold BKLNW.v1.a₂
  exact mul_nonneg (by norm_num) (le_max_of_le_left (BKLNW_f_nonneg (exp_pos _).le))

/-- The multiplier this file computes with is the one `FKS2Numerics.v1` states a bound for.

They differ only in that the node has `log(e³⁰)` already reduced to `30`, a conclusion not being
allowed to mention anything defined in a solution. -/
theorem nuAsymp_e30_eq :
    nuAsymp 121.096 (3 / 2) 2 5.5666305 (1 + 1.93378e-8) (BKLNW.v1.a₂ 30) (exp 30)
      = FKS2Numerics.v1.nuAsympE30 := by
  unfold FKS2.v2.nuAsymp FKS2Numerics.v1.nuAsympE30
  rw [Real.log_exp]

/-- The admissible bound in the same factored form, `A · R^{-B} · (log x)^B exp(-(C/√R)√(log x))`.

`(log x / R)^B` splits as `(log x)^B R^{-B}`, and `(log x / R)^{1/2}` as `√(log x)/√R`, which is
where the `C/√R` throughout `Growth.lean` comes from. -/
theorem admissibleBound_eq_g_mul {A B C R x : ℝ} (hR : 0 < R) (hx : 1 < x) :
    admissibleBound A B C R x
      = A * R ^ (-B) * ((log x) ^ B * exp (-(C / sqrt R) * sqrt (log x))) := by
  have hlog : 0 < log x := log_pos hx
  unfold admissibleBound
  rw [div_rpow hlog.le hR.le, ← sqrt_eq_rpow, sqrt_div hlog.le, rpow_neg hR.le]
  have : -C * (sqrt (log x) / sqrt R) = -(C / sqrt R) * sqrt (log x) := by ring
  rw [this]
  field_simp

theorem continuousOn_inv_log {x : ℝ} (hx : 2 ≤ x) (n : ℕ) :
    ContinuousOn (fun t : ℝ => 1 / (log t) ^ n) (Set.uIcc 2 x) := by
  rw [Set.uIcc_of_le hx]
  intro t ht
  have ht1 : (1 : ℝ) < t := by linarith [ht.1]
  have hlog : 0 < log t := log_pos ht1
  have hne : (log t) ^ n ≠ 0 := pow_ne_zero _ hlog.ne'
  exact ((continuousAt_const.div ((continuousAt_log (by linarith)).pow n) hne)).continuousWithinAt

end FKS2Sol
