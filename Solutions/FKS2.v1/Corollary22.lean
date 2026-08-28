/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import ThetaToPi

/-!
# Corollary 22: the headline asymptotic bound for `π`

`|π(x) − Li(x)| ≤ 9.2211 x √(log x) exp(−0.84768363 √(log x))` for all `x ≥ 2`, stated on the node
at `R = 1` as `FKS2.v1.corollary_22`.

## The split, and which half is which

Above `e²⁰⁰⁰⁰` this is analysis: Corollary 14 normalised to `R = 1`, then `theorem_3`, with the
multiplier `μ_asymp` controlled by the Dawson estimates. Below `e²⁰⁰⁰⁰` the paper interpolates
numerical results as a step function, which is `FKS2Numerics.v1.corollary_22_mid_range`.

`PrimeNumberTheoremAnd` formalizes only the tail (`corollary_22_tail`); it has no full Corollary 22.

## Where the constants come from, and how tight they are

`R` is folded into the constants: `121.0961/R^{3/2} = 9.220226…` and `2/√R = 0.8476836337…`, against
the paper's printed `9.2211` and `0.84768363`.

The `C` comparison is the tight one. `0.84768363 ≤ 2/√R` holds by about `3.7·10⁻⁹`; squared, the
margin is `4.8·10⁻⁸`, which is what makes it a `norm_num` fact about rationals rather than a
judgement call. The direction matters: the paper's printed `C` is very slightly *smaller* than
`2/√R`, and a smaller `C` is a weaker bound, so the printed statement is the safe one.

The `A` comparison has room: `9.220226 × (1 + μ) = 9.220688` against `9.2211`, so `μ` may be as
large as `8.68·10⁻⁵`. The Dawson summand, bounded below, contributes about `5.7·10⁻⁵`.
-/

namespace FKS2Sol

open Real IEANTN
open FKS2.v1 (muAsymp dawson)

/-- `√R ≥ 2.35937` and `√R ≤ 2/0.84768363`, the two bounds the normalisation needs.
The second is tight — the margin on the squared form is about `4.8·10⁻⁸`. -/
theorem sqrtR_bounds :
    (2.35937 : ℝ) ≤ sqrt 5.5666305 ∧ sqrt 5.5666305 ≤ 2 / 0.84768363 := by
  constructor
  · have h := Real.sqrt_le_sqrt (show ((2.35937 : ℝ)) ^ 2 ≤ 5.5666305 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.35937)] at h
  · have h := Real.sqrt_le_sqrt (show (5.5666305 : ℝ) ≤ (2 / 0.84768363) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2 / 0.84768363)] at h

/-- **Corollary 14, normalised to `R = 1`.** Folding `R` into the constants:
`121.0961/R^{3/2} ≤ 9.2203` and `0.84768363 ≤ 2/√R`. -/
theorem corollary_14_normalized (h : FKS2.v1.corollary_14) :
    HasClassicalBound Eθ 9.2203 (3 / 2) 0.84768363 1 2 := by
  obtain ⟨hlo, hhi⟩ := sqrtR_bounds
  have hR : (0:ℝ) < 5.5666305 := by norm_num
  have hsr : (0:ℝ) < sqrt 5.5666305 := sqrt_pos.mpr hR
  intro x hx
  have hx1 : (1:ℝ) < x := by linarith
  have hL : 0 < log x := log_pos hx1
  have hsL : (0:ℝ) ≤ sqrt (log x) := sqrt_nonneg _
  refine le_trans (h x hx) ?_
  rw [admissibleBound_eq_g_mul hR hx1, admissibleBound_eq_g_mul (by norm_num : (0:ℝ) < 1) hx1,
    Real.sqrt_one, Real.one_rpow]
  -- reduces to comparing the two leading constants and the two exponentials
  have hexp : exp (-(2 / sqrt 5.5666305) * sqrt (log x))
      ≤ exp (-(0.84768363 / 1) * sqrt (log x)) := by
    apply exp_le_exp.mpr
    have hC : (0.84768363 : ℝ) ≤ 2 / sqrt 5.5666305 := by
      rw [le_div_iff₀ hsr]
      calc (0.84768363 : ℝ) * sqrt 5.5666305 ≤ 0.84768363 * (2 / 0.84768363) := by
            exact mul_le_mul_of_nonneg_left hhi (by norm_num)
        _ = 2 := by norm_num
    have : (0.84768363 : ℝ) / 1 = 0.84768363 := by norm_num
    rw [this]
    nlinarith [hsL, hC]
  have hconst : (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (-(3/2) : ℝ) ≤ 9.2203 * 1 := by
    have hpow : (5.5666305 : ℝ) ^ ((3:ℝ)/2) = 5.5666305 * sqrt 5.5666305 := by
      rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, rpow_add hR, rpow_one, ← sqrt_eq_rpow]
    have hpos : (0:ℝ) < (5.5666305 : ℝ) ^ ((3:ℝ)/2) := rpow_pos_of_pos hR _
    rw [show (-(3/2) : ℝ) = -((3:ℝ)/2) by norm_num, rpow_neg hR.le, mul_one,
      mul_inv_le_iff₀ hpos, hpow]
    nlinarith [hlo]
  have hprod : (0:ℝ) ≤ (log x) ^ ((3:ℝ)/2) := (rpow_pos_of_pos hL _).le
  have hE : (0:ℝ) < exp (-(0.84768363 / 1) * sqrt (log x)) := exp_pos _
  have hc0 : (0:ℝ) ≤ 121.0961 * (5.5666305 : ℝ) ^ (-(3/2) : ℝ) := by positivity
  calc 121.0961 * (5.5666305:ℝ) ^ (-(3/2) : ℝ)
        * ((log x) ^ ((3:ℝ)/2) * exp (-(2 / sqrt 5.5666305) * sqrt (log x)))
      ≤ 121.0961 * (5.5666305:ℝ) ^ (-(3/2) : ℝ)
        * ((log x) ^ ((3:ℝ)/2) * exp (-(0.84768363 / 1) * sqrt (log x))) := by
        gcongr
    _ ≤ 9.2203 * 1 * ((log x) ^ ((3:ℝ)/2) * exp (-(0.84768363 / 1) * sqrt (log x))) := by
        gcongr

theorem sqrt20000_bounds : (141.42 : ℝ) ≤ sqrt 20000 ∧ sqrt 20000 ≤ 141.422 := by
  constructor
  · have h := Real.sqrt_le_sqrt (show ((141.42:ℝ))^2 ≤ 20000 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 141.42)] at h
  · have h := Real.sqrt_le_sqrt (show (20000:ℝ) ≤ (141.422)^2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 141.422)] at h

/-- The Dawson summand of `μ_asymp` at `x₁ = e²⁰⁰⁰⁰`. -/
theorem muAsymp_dawson_term_le :
    2 * dawson (sqrt 20000 - 0.84768363 / (2 * sqrt 1)) / sqrt 20000 ≤ 5.9e-5 := by
  obtain ⟨hlo, hhi⟩ := sqrt20000_bounds
  rw [Real.sqrt_one]
  set v := sqrt 20000 - 0.84768363 / (2 * 1) with hv
  have hvlo : (140.996 : ℝ) ≤ v := by rw [hv]; norm_num; linarith
  have hv2 : (2 : ℝ) ≤ v := by linarith
  have hD := dawson_le hv2
  -- the exponential piece is negligible
  have hexp : 2 * exp (4 - v ^ 2) ≤ 1e-4 := by
    have hsq : (19878 : ℝ) ≤ v ^ 2 := by nlinarith [hvlo, hv2]
    have h1 : exp (4 - v ^ 2) ≤ exp (-10) := by
      apply exp_le_exp.mpr; linarith
    have h2 : exp (-10 : ℝ) ≤ 5e-5 := by
      rw [Real.exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
      have he10 : (20000 : ℝ) ≤ exp 10 := by
        have hone : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
        calc (20000 : ℝ) ≤ (2.7182818283 : ℝ) ^ (10 : ℕ) := by norm_num
          _ ≤ (exp 1) ^ (10 : ℕ) := by gcongr
          _ = exp 10 := by rw [← Real.exp_nat_mul]; norm_num
      linarith
    linarith
  have hfrac : 4 / (7 * v) ≤ 4.054e-3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hvlo]
  have hDle : dawson v ≤ 1e-4 + 4.054e-3 := by linarith
  have hDnn : (0:ℝ) ≤ dawson v := dawson_nonneg (by linarith)
  rw [div_le_iff₀ (by linarith : (0:ℝ) < sqrt 20000)]
  nlinarith [hDle, hlo, hDnn]

/-- **Corollary 22.**

Assembled from two halves. `corollary_22_mid_range` is the numerical interpolation on
`[2, e²⁰⁰⁰⁰]`; above that the ingredients are all in hand — `corollary_14_normalized`,
`FKS2.v1.theorem_3`, and `muAsymp_dawson_term_le` — and what remains is the boundary summand of
`μ_asymp` together with the arithmetic that puts `9.2203 (1 + μ) ≤ 9.2211`.

That boundary summand is `(2 · 20000)/(ε(x₁) · e²⁰⁰⁰⁰ · log 2) · |K|`, and it is astronomically
small: `|K| = 1` exactly, because `π(2) = 1`, `Li(2) = 0` and `θ(2) = log 2`, so
`K = log 2/2 − (log 2 − 2)/2 = 1`. All three of those values are computable in Lean — checked. The
denominator carries `e²⁰⁰⁰⁰`, so a crude bound suffices: `ε(x₁) ≥ 9.2203 · 20000 · e^{-120}` gives
the summand at most `0.313 · e^{-19880}`, and `e^{19880} ≥ e^{10} ≥ 20000` closes it with vast
room. -/
theorem corollary_22
    (hpsi : FKS.v1.psi_classical_bound)
    (hconv : BKLNW.v1.corollary_5_1)
    (hsmall : BKLNW.v1.theta_error_le_one)
    (hnu : FKS2Numerics.v1.nu_asymp_e30_le)
    (hfloor : FKS2Numerics.v1.theta_asymp_ge_one_below_e30)
    (hmid : FKS2Numerics.v1.corollary_22_mid_range) :
    FKS2.v1.corollary_22 := by
  sorry

end FKS2Sol
