/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Corollary22

/-!
# Corollary 23 — Table 6, row 2

`Eπ` obeys the classical bound with `A = 0.826`, `B = 1/4`, `C = 1`, `R = 5.5666305`, for `x ≥ e`.

## Three ranges, and only the last is analysis

* `[e, e⁶]` — `FKS2Numerics.v1.table6_row2_floor`, a direct check on `x ∈ [2.72, 403]`;
* `[e⁶, e²⁰⁰⁰⁰]` — `FKS2Numerics.v1.corollary_23_mid_range`, the paper's numerical work;
* `[e²⁰⁰⁰⁰, ∞)` — **Corollary 22 dominates the row-2 curve**, proved below.

This is why Corollary 22 was worth doing first. It does *not* follow from Theorem 3 — that preserves
`B` and `C`, and needs `B ≥ 3/2`, while this row is `B = 1/4`, `C = 1`. And Corollary 22 does not
dominate on all of `[e, ∞)`: the ratio peaks near `118.9` at `x ≈ e^34.8`. It does dominate from
about `x ≈ e^671`, and `e²⁰⁰⁰⁰` is comfortably past that.
-/

namespace FKS2Sol

open Real IEANTN

/-- Beyond `e²⁰⁰⁰⁰`, Corollary 22's bound is below Table 6's row-2 curve.

Writing `s = √(log x)`, the claim is `9.2211 s³ e^{-c₁s} ≤ 0.826 R^{-1/4} √s e^{-c₂s}` with
`c₁ = 0.84768363` and `c₂ = 1/√R`. Since `√s ≥ 1` it suffices to compare without it, and then
`e^u ≥ u⁶/720` turns the exponential into a sixth power — enough because `s ≥ 141.42` while the
inequality only needs `s ≥ 128.7`. A fourth power is *not* enough; it would need `s ≥ 12750`. -/
theorem corollary_22_dominates_row2 {x : ℝ} (hx : exp 20000 ≤ x) :
    admissibleBound 9.2211 (3 / 2) 0.84768363 1 x
      ≤ admissibleBound 0.826 0.25 1 5.5666305 x := by
  have hx1 : (1 : ℝ) < x := by
    have : (2 : ℝ) ≤ exp 20000 := by nlinarith [Real.add_one_le_exp (20000 : ℝ)]
    linarith
  have hL : (20000 : ℝ) ≤ log x := by
    rw [← Real.log_exp 20000]; exact log_le_log (exp_pos _) hx
  have hLpos : 0 < log x := by linarith
  set s := sqrt (log x) with hs
  have hs2 : s ^ 2 = log x := Real.sq_sqrt hLpos.le
  have hslo : (141.42 : ℝ) ≤ s := by
    have h := Real.sqrt_le_sqrt (show ((141.42 : ℝ)) ^ 2 ≤ log x by nlinarith [hL])
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 141.42)] at h
  have hspos : (0 : ℝ) < s := by linarith
  have hR : (0 : ℝ) < 5.5666305 := by norm_num
  have hsr : (2.35937 : ℝ) ≤ sqrt 5.5666305 := by
    have h := Real.sqrt_le_sqrt (show ((2.35937 : ℝ)) ^ 2 ≤ 5.5666305 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.35937)] at h
  have hR14 : (5.5666305 : ℝ) ^ (0.25 : ℝ) ≤ 1.5362 := by
    have h : ((5.5666305 : ℝ)) ^ (0.25 : ℝ) ≤ ((1.5362 : ℝ) ^ (4 : ℕ)) ^ (0.25 : ℝ) := by
      gcongr
      norm_num
    calc ((5.5666305 : ℝ)) ^ (0.25 : ℝ) ≤ ((1.5362 : ℝ) ^ (4 : ℕ)) ^ (0.25 : ℝ) := h
      _ = 1.5362 := by
          rw [← rpow_natCast (1.5362 : ℝ) 4, ← rpow_mul (by norm_num : (0:ℝ) ≤ 1.5362)]
          norm_num
  have hR14pos : (0 : ℝ) < (5.5666305 : ℝ) ^ (0.25 : ℝ) := rpow_pos_of_pos hR _
  have hL32 : (log x / 1) ^ ((3 : ℝ) / 2) = (sqrt (log x)) ^ 3 := by
    rw [show (log x / 1) = log x by ring, Real.sqrt_eq_rpow, ← rpow_natCast _ 3,
      ← rpow_mul hLpos.le]
    norm_num
  have hL14 : (log x / 5.5666305) ^ (0.25 : ℝ)
      = sqrt (sqrt (log x)) / (5.5666305 : ℝ) ^ (0.25 : ℝ) := by
    rw [div_rpow hLpos.le hR.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← rpow_mul hLpos.le]
    norm_num
  have hL12 : (log x / 5.5666305) ^ ((1 : ℝ) / 2) = sqrt (log x) / sqrt 5.5666305 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div hLpos.le]
  have hL12' : (log x / 1) ^ ((1 : ℝ) / 2) = sqrt (log x) := by
    rw [show (log x / 1) = log x by ring, ← Real.sqrt_eq_rpow]
  unfold admissibleBound
  rw [hL32, hL14, hL12, hL12']
  set s := sqrt (log x) with hsdef
  have hspos : (0 : ℝ) < s := by
    rw [hsdef]; exact Real.sqrt_pos.mpr hLpos
  have hslo : (141.42 : ℝ) ≤ s := by
    have h := Real.sqrt_le_sqrt (show ((141.42 : ℝ)) ^ 2 ≤ log x by nlinarith [hL])
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 141.42), ← hsdef] at h
  have hsrpos : (0 : ℝ) < sqrt 5.5666305 := by linarith
  -- `e^u ≥ u⁶/720` is what makes the exponential beat `s³`; `u⁴/24` would not.
  have hpow : (0.4238411 * s) ^ 6 / 720 ≤ exp (0.4238411 * s) := by
    have hnn : (0 : ℝ) ≤ 0.4238411 * s := by positivity
    have h : (0.4238411 * s) ^ 6 / (Nat.factorial 6 : ℝ) ≤ exp (0.4238411 * s) :=
      Real.pow_div_factorial_le_exp (0.4238411 * s) hnn 6
    have hf : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
    rwa [hf] at h
  have hs3 : (2.828e6 : ℝ) ≤ s ^ 3 := by nlinarith [hslo, hspos]
  have hs6 : (2.828e6 : ℝ) * s ^ 3 ≤ s ^ 6 := by nlinarith [hs3, hspos]
  have hmain : 9.2211 * s ^ 3 ≤ 0.53768 * exp (0.4238411 * s) := by
    nlinarith [hpow, hs6, hspos, hs3]
  have hE1 : (0 : ℝ) < exp (-0.84768363 * s) := exp_pos _
  have hcomb : exp (0.4238411 * s) * exp (-0.84768363 * s) = exp (-0.42384253 * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have hstep : 9.2211 * s ^ 3 * exp (-0.84768363 * s) ≤ 0.53768 * exp (-0.42384253 * s) := by
    have hm := mul_le_mul_of_nonneg_right hmain hE1.le
    calc 9.2211 * s ^ 3 * exp (-0.84768363 * s)
        ≤ 0.53768 * exp (0.4238411 * s) * exp (-0.84768363 * s) := hm
      _ = 0.53768 * exp (-0.42384253 * s) := by rw [mul_assoc, hcomb]
  -- the row-2 side is at least `0.53768 e^{-s/√R}`
  have hexp2 : exp (-0.42384253 * s) ≤ exp (-1 * (s / sqrt 5.5666305)) := by
    refine exp_le_exp.mpr ?_
    have h1 : s / sqrt 5.5666305 ≤ 0.42384253 * s := by
      rw [div_le_iff₀ hsrpos]
      nlinarith [hsr, hspos]
    linarith
  have hsq1 : (1 : ℝ) ≤ sqrt s := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ s by linarith)
    simpa using h
  have hE2 : (0 : ℝ) < exp (-1 * (s / sqrt 5.5666305)) := exp_pos _
  have hfrac : (0.53768 : ℝ) ≤ 0.826 * (sqrt s / (5.5666305 : ℝ) ^ (0.25 : ℝ)) := by
    have hq : (0 : ℝ) < (5.5666305 : ℝ) ^ (0.25 : ℝ) := hR14pos
    rw [mul_div_assoc', le_div_iff₀ hq]
    nlinarith [hR14, hsq1, hq]
  calc 9.2211 * s ^ 3 * exp (-0.84768363 * s)
      ≤ 0.53768 * exp (-0.42384253 * s) := hstep
    _ ≤ 0.53768 * exp (-1 * (s / sqrt 5.5666305)) := by
        exact mul_le_mul_of_nonneg_left hexp2 (by norm_num)
    _ ≤ 0.826 * (sqrt s / (5.5666305 : ℝ) ^ (0.25 : ℝ)) * exp (-1 * (s / sqrt 5.5666305)) :=
        mul_le_mul_of_nonneg_right hfrac hE2.le

/-- **Corollary 23**, Table 6's row 2: `Eπ` obeys the classical bound with `A = 0.826`,
`B = 1/4`, `C = 1`, `R = 5.5666305`, for all `x ≥ e`.

Three ranges, and only the last is analysis. -/
theorem corollary_23
    (hpsi : FKS.v1.psi_classical_bound)
    (hconv : BKLNW.v1.corollary_5_1)
    (hsmall : BKLNW.v1.theta_error_le_one)
    (hnu : FKS2Numerics.v1.nu_asymp_e30_le)
    (hthfloor : FKS2Numerics.v1.theta_asymp_ge_one_below_e30)
    (hmid22 : FKS2Numerics.v1.corollary_22_mid_range)
    (hfloor : FKS2Numerics.v1.table6_row2_floor)
    (hmid23 : FKS2Numerics.v1.corollary_23_mid_range)
    (hprop13 : FKS2.v2.proposition_13)
    (hthm3 : FKS2.v2.theorem_3) :
    FKS2.v1.corollary_23 := by
  intro x hx
  by_cases h6 : x ≤ exp 6
  · have hf := hfloor x ⟨hx, h6⟩
    simp only [IEANTN.margin, pow_zero, one_mul] at hf
    exact hf
  · have h6' : exp 6 ≤ x := le_of_not_ge h6
    by_cases h20k : x ≤ exp 20000
    · have hm := hmid23 x ⟨h6', h20k⟩
      simp only [IEANTN.margin, pow_zero, one_mul] at hm
      exact hm
    · have h20k' : exp 20000 ≤ x := le_of_not_ge h20k
      have h22 := corollary_22 hpsi hconv hsmall hnu hthfloor hmid22 hprop13 hthm3
      exact le_trans (h22 x (by
        have : (2 : ℝ) ≤ exp 20000 := by nlinarith [Real.add_one_le_exp (20000 : ℝ)]
        linarith)) (corollary_22_dominates_row2 h20k')

end FKS2Sol
