/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Corollary14
import Dawson

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
open FKS2.v2 (muAsymp dawson)
open FKS2.v2 (muAsymp dawson)

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

/-- The Table 6 row-2 curve never exceeds `0.4298`.

Elementary, with no numerical input. Writing `u = √(log x / R)`, the bound is `0.826 √u e^{-u}`;
then `e^{-u} ≤ 1/(1+u)` and `2√u ≤ 1 + u` give `0.826/2 = 0.413`. The true supremum is `0.3543`,
at `u = 1/2`, so there is room to spare. -/
theorem admissibleBound_row2_le {x : ℝ} (hx : 1 < x) :
    admissibleBound 0.826 0.25 1 5.5666305 x ≤ 0.4298 := by
  have hL : 0 < log x := log_pos hx
  have hw0 : (0:ℝ) ≤ log x / 5.5666305 := by positivity
  have hq : (log x / 5.5666305) ^ ((1:ℝ)/2) = sqrt (log x / 5.5666305) :=
    (sqrt_eq_rpow _).symm
  have hq4 : (log x / 5.5666305) ^ (0.25:ℝ) = sqrt (sqrt (log x / 5.5666305)) := by
    rw [show (0.25:ℝ) = (1/2) * (1/2) by norm_num, rpow_mul hw0, ← sqrt_eq_rpow, ← sqrt_eq_rpow]
  unfold admissibleBound
  rw [hq, hq4]
  set u := sqrt (log x / 5.5666305) with hu
  have hu0 : (0:ℝ) ≤ u := sqrt_nonneg _
  have hsu : (0:ℝ) ≤ sqrt u := sqrt_nonneg _
  have hsu2 : sqrt u ^ 2 = u := Real.sq_sqrt hu0
  -- e^{-u} ≤ 1/(1+u)
  have hexp : exp (-1 * u) ≤ 1 / (1 + u) := by
    rw [show (-1:ℝ) * u = -u by ring, Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (exp_pos _)]
    have := Real.add_one_le_exp u
    have h1u : (0:ℝ) < 1 + u := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h1u]
    linarith
  -- 2√u ≤ 1 + u
  have hAM : 2 * sqrt u ≤ 1 + u := by nlinarith [sq_nonneg (sqrt u - 1), hsu2]
  have h1u : (0:ℝ) < 1 + u := by linarith
  calc 0.826 * sqrt u * exp (-1 * u)
      ≤ 0.826 * sqrt u * (1 / (1 + u)) := by
        apply mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 0.4298 := by
        rw [mul_one_div, div_le_iff₀ h1u]
        nlinarith [hAM]

/-- `log x / x ≤ 1/e`, from `log (x/e) ≤ x/e - 1`. -/
theorem log_div_self_le {x : ℝ} (hx : 0 < x) : log x / x ≤ 1 / exp 1 := by
  have he : (0:ℝ) < exp 1 := exp_pos 1
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < x / exp 1 by positivity)
  rw [Real.log_div hx.ne' he.ne', Real.log_exp] at h
  -- `h : log x - 1 ≤ x / exp 1 - 1`; clear the division before comparing.
  have h' : log x ≤ x / exp 1 := by linarith
  rw [le_div_iff₀ he] at h'
  rw [div_le_div_iff₀ hx he]
  linarith

/-- On `[2, e)` the estimate is direct, with no numerical input.

`π(x) = 1` there, `0 ≤ Li(x) ≤ 2`, so `|π(x) − Li(x)| ≤ 1`; and `Eπ(x) = |π − Li|·(log x/x)` with
`log x/x ≤ 1/e`. So `Eπ(x) ≤ 1/e ≈ 0.3679`. -/
theorem Epi_le_on_two_e {x : ℝ} (hx : 2 ≤ x) (hlt : x < exp 1) : Eπ x ≤ 0.4298 := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hL : 0 < log x := log_pos hx1
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have he3 : exp 1 < 3 := Real.exp_one_lt_three
  -- π(x) = 1
  have hfl : ⌊x⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by linarith)]
    constructor
    · exact_mod_cast hx
    · push_cast; linarith
  have hpi : primeCounting x = 1 := by
    unfold primeCounting
    rw [hfl]
    norm_num
    decide +kernel
  -- 0 ≤ Li x ≤ 2
  have hint : IntervalIntegrable (fun t : ℝ => 1 / log t) MeasureTheory.volume 2 x := by
    have := (continuousOn_inv_log hx 1).intervalIntegrable (μ := MeasureTheory.volume)
    simpa using this
  have hLi0 : 0 ≤ Li x := by
    unfold Li
    refine intervalIntegral.integral_nonneg hx fun t ht ↦ ?_
    have : 0 < log t := log_pos (by linarith [ht.1])
    positivity
  have hLi2 : Li x ≤ 2 := by
    unfold Li
    have hmono : (∫ t in (2:ℝ)..x, 1 / log t) ≤ ∫ _t in (2:ℝ)..x, 1 / log 2 := by
      refine intervalIntegral.integral_mono_on hx hint
        (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _) fun t ht ↦ ?_
      have h2t : (2:ℝ) ≤ t := ht.1
      have hlt2 : 0 < log t := log_pos (by linarith)
      apply one_div_le_one_div_of_le hl2
      exact log_le_log (by norm_num) h2t
    rw [intervalIntegral.integral_const] at hmono
    have hlog2 : (0.6931471803 : ℝ) < log 2 := Real.log_two_gt_d9
    have hxb : x - 2 < 1 := by linarith
    have : (x - 2) • (1 / log 2) ≤ 2 := by
      rw [smul_eq_mul, mul_one_div, div_le_iff₀ hl2]
      nlinarith [hxb, hlog2]
    linarith
  have habs : |primeCounting x - Li x| ≤ 1 := by
    rw [hpi, abs_le]; constructor <;> linarith
  -- assemble
  have hkey : Eπ x = |primeCounting x - Li x| * (log x / x) := by
    unfold Eπ; field_simp
  rw [hkey]
  have hlx : log x / x ≤ 1 / exp 1 := log_div_self_le hxpos
  have hepos : (0:ℝ) < exp 1 := exp_pos 1
  have hnn : (0:ℝ) ≤ log x / x := by positivity
  calc |primeCounting x - Li x| * (log x / x) ≤ 1 * (log x / x) := by
        apply mul_le_mul_of_nonneg_right habs hnn
    _ ≤ 1 * (1 / exp 1) := by apply mul_le_mul_of_nonneg_left hlx (by norm_num)
    _ ≤ 0.4298 := by
        rw [one_mul, div_le_iff₀ hepos]
        nlinarith [Real.exp_one_gt_d9]

/-- `K = 1` exactly at `x₀ = 2`: `π(2) = 1`, `Li(2) = 0` and `θ(2) = log 2`, so
`K = log 2/2 − (log 2 − 2)/2 = 1`. -/
theorem boundary_constant_eq_one :
    |(primeCounting 2 - Li 2) / (2 / log 2) - (Chebyshev.theta 2 - 2) / 2| = 1 := by
  have hpi : primeCounting 2 = 1 := by
    unfold primeCounting
    norm_num
    decide +kernel
  have hli : Li 2 = 0 := by unfold Li; simp
  have hth : Chebyshev.theta 2 = log 2 := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    norm_num [Nat.primesLE]
    rw [show Nat.primesBelow 3 = {2} from by decide]
    simp
  have hl2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  rw [hpi, hli, hth]
  rw [show ((1 : ℝ) - 0) / (2 / log 2) - (log 2 - 2) / 2 = 1 by field_simp; ring]
  norm_num

/-- The whole of `μ_asymp` at `x₀ = 2`, `x₁ = e²⁰⁰⁰⁰`, bounded below `8.67·10⁻⁵`.

The boundary summand carries `e²⁰⁰⁰⁰` in its denominator and is crushed to nothing; the Dawson
summand is what the estimate actually costs, at about `5.7·10⁻⁵`. -/
theorem muAsymp_boundary_and_dawson_le :
    FKS2.v2.muAsymp 9.2203 (3 / 2) 0.84768363 1 2 (exp 20000) ≤ 8.67e-5 := by
  have hl2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := Real.log_two_gt_d9
  obtain ⟨hs20lo, hs20hi⟩ := sqrt20000_bounds
  unfold FKS2.v2.muAsymp
  rw [Real.log_exp, boundary_constant_eq_one, mul_one]
  -- the Dawson summand
  have hdaw : 2 * dawson (sqrt 20000 - 0.84768363 / (2 * sqrt 1)) / sqrt 20000 ≤ 5.9e-5 :=
    muAsymp_dawson_term_le
  -- the boundary summand: bound the admissible bound below, then the whole quotient above
  have hR1 : (0 : ℝ) < 1 := one_pos
  have hpow : (20000 : ℝ) ≤ (20000 : ℝ) ^ ((3 : ℝ) / 2) := by
    nth_rewrite 1 [show (20000 : ℝ) = (20000 : ℝ) ^ (1 : ℝ) from (rpow_one _).symm]
    exact rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hexpge : exp (-120 : ℝ) ≤ exp (-0.84768363 * (20000 / 1) ^ ((1 : ℝ) / 2)) := by
    refine exp_le_exp.mpr ?_
    rw [show ((20000 : ℝ) / 1) = 20000 by norm_num, ← Real.sqrt_eq_rpow]
    nlinarith [hs20hi]
  have hlow : (184406 : ℝ) * exp (-120) ≤ admissibleBound 9.2203 (3 / 2) 0.84768363 1 (exp 20000) := by
    unfold admissibleBound
    rw [Real.log_exp, show ((20000 : ℝ) / 1) = 20000 by norm_num]
    have h1 : (0 : ℝ) < exp (-0.84768363 * (20000 : ℝ) ^ ((1 : ℝ) / 2)) := exp_pos _
    have h2 : (0 : ℝ) < (20000 : ℝ) ^ ((3 : ℝ) / 2) := rpow_pos_of_pos (by norm_num) _
    have hexpge' : exp (-120 : ℝ) ≤ exp (-0.84768363 * (20000 : ℝ) ^ ((1 : ℝ) / 2)) := by
      simpa [show ((20000 : ℝ) / 1) = 20000 by norm_num] using hexpge
    nlinarith [hpow, hexpge', exp_pos (-120 : ℝ)]
  have hepos : (0 : ℝ) < admissibleBound 9.2203 (3 / 2) 0.84768363 1 (exp 20000) := by
    have : (0 : ℝ) < 184406 * exp (-120) := by positivity
    linarith
  -- exp 19880 is enormous; that is all the boundary summand needs
  have he10 : (20000 : ℝ) ≤ exp 10 := by
    have hone : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
    calc (20000 : ℝ) ≤ (2.7182818283 : ℝ) ^ (10 : ℕ) := by norm_num
      _ ≤ (exp 1) ^ (10 : ℕ) := by gcongr
      _ = exp 10 := by rw [← Real.exp_nat_mul]; norm_num
  have hbig : (20000 : ℝ) ≤ exp 19880 := le_trans he10 (exp_le_exp.mpr (by norm_num))
  have hprod : (127794 : ℝ) * exp 19880 ≤
      admissibleBound 9.2203 (3 / 2) 0.84768363 1 (exp 20000) * exp 20000 * log 2 := by
    -- Do not rewrite `exp 20000` in the goal: it also occurs as the ARGUMENT of `admissibleBound`,
    -- and rewriting there turns the two sides into different atoms.
    have hE : (0 : ℝ) < exp 19880 := exp_pos _
    have hcancel : exp (-120 : ℝ) * exp 20000 = exp 19880 := by
      rw [← Real.exp_add]; norm_num
    have hpos : (0 : ℝ) < exp 20000 * log 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hlow hpos.le
    have hlhs : (184406 : ℝ) * exp (-120) * (exp 20000 * log 2)
        = 184406 * exp 19880 * log 2 := by
      rw [show (184406 : ℝ) * exp (-120) * (exp 20000 * log 2)
            = 184406 * (exp (-120) * exp 20000) * log 2 by ring, hcancel]
    rw [hlhs] at hmul
    nlinarith [hmul, hE, hlog2]
  have hterm1 : (2 * 20000) / (admissibleBound 9.2203 (3 / 2) 0.84768363 1 (exp 20000)
      * exp 20000 * log 2) ≤ 2.7e-5 := by
    rw [div_le_iff₀ (by positivity)]
    calc (2 : ℝ) * 20000 = 40000 := by norm_num
      _ ≤ 2.7e-5 * (127794 * exp 19880) := by nlinarith [hbig]
      _ ≤ 2.7e-5 * (admissibleBound 9.2203 (3 / 2) 0.84768363 1 (exp 20000) * exp 20000 * log 2) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
  rw [Real.sqrt_one] at hdaw ⊢
  linarith [hterm1, hdaw]

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
    (hmid : FKS2Numerics.v1.corollary_22_mid_range)
    (hprop13 : FKS2.v2.proposition_13)
    (hthm3 : FKS2.v2.theorem_3) :
    FKS2.v1.corollary_22 := by
  intro x hx
  by_cases hle : x ≤ exp 20000
  · exact hmid x ⟨hx, hle⟩
  · have hgt : exp 20000 < x := lt_of_not_ge hle
    have hx1 : (1 : ℝ) < x := by linarith
    have hlog2 : (0.6931471803 : ℝ) < log 2 := Real.log_two_gt_d9
    have hsq2 : (0.8325 : ℝ) ≤ sqrt (log 2) := by
      have h := Real.sqrt_le_sqrt (show ((0.8325 : ℝ)) ^ 2 ≤ log 2 by nlinarith [hlog2])
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0.8325)] at h
    have h14 : FKS2.v1.corollary_14 := corollary_14 hprop13 hpsi hconv hsmall hnu hfloor
    have htail := hthm3 9.2203 (3 / 2) 0.84768363 1 2 (exp 20000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Real.sqrt_one]; linarith)
      (by
        rw [Real.sqrt_one, max_le_iff]
        constructor
        · nlinarith [Real.add_one_le_exp (20000 : ℝ)]
        · exact Real.exp_le_exp.mpr (by norm_num))
      (corollary_14_normalized h14)
    refine (htail x hgt.le).trans ?_
    refine admissibleBound_mono_A (by norm_num) hx1 ?_
    -- `(1 + μ) · 9.2203 ≤ 9.2211`, i.e. `μ ≤ 8.67e-5`.
    have hmu := muAsymp_boundary_and_dawson_le
    unfold FKS2.v2.muAsymp at hmu ⊢
    nlinarith [hmu]

end FKS2Sol
