/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.FKS2.v2.Conclusions
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Dawson function

`D₊(x) = e^{-x²} ∫₀ˣ e^{t²} dt`, the paper's (Dawson).

It appears because the substitution `u = √(log t)` turns the integral of an admissible bound into
`∫ u^{2B-3} exp(u² - Cu/√R) du`, and bounding `u^{2B-3}` by its maximum leaves exactly a Dawson
integral. So `D₊` is not decoration: it is what the `θ → π` conversion's constant is made of, and
Theorem 3 cannot even be *stated* without it.

Mathlib has no Dawson function. It is defined on the node, as `FKS2.v2.dawson`, because
`FKS2.v1.theorem_3` cannot be stated without it; this file proves things about that definition
rather than introducing a second one.

## What is needed of it, and what is not

Theorem 3 only ever *evaluates* `D₊`, so for its statement nothing is required beyond the
definition. The paper additionally records that `D₊` has a single maximum near `0.9241` and
decreases after it, which its proof uses to bound the tail.

That fact rests on the differential equation `D₊'(x) + 2x D₊(x) = 1`, which is proved below —
`hasDerivAt_dawson` — and it is proved here too, as `dawson_strictAntiOn`.

The route taken is not the paper's. The paper argues that every positive critical point is a strict
local maximum, so there is at most one, so `D₊` decreases after it — correct, but awkward to
formalize, and it leaves the maximum's location as a separate numerical question. Instead
`inv_lt_dawson` establishes `D₊(v) > 1/(2v)` for `v ≥ 1` directly, which by the differential
equation *is* `D₊'(v) < 0`. The proof is that `∫₀ᵛ e^{t²} dt - e^{v²}/(2v)` has derivative
`e^{v²}/(2v²) > 0`, so it suffices to check `v = 1`, where `e^{t²} ≥ 1 + t² + t⁴/2` gives
`∫₀¹ ≥ 43/30 > e/2`. No numerical input beyond Mathlib's own bound on `e`.

`dawson_shift_div_antitoneOn` is the combination Theorem 3 actually consumes, and it is where the
paper's threshold `x₁ ≥ exp((1 + C/(2√R))²)` comes from: the `1` is exactly what clears the Dawson
maximum.

## An upper bound too

`inv_lt_dawson` says `D₊(v) > 1/(2v)`; `dawson_le` is the companion, `D₊(v) ≤ 2e^{4-v²} + 4/(7v)`
for `v ≥ 2`. Corollary 22 needs it, because `μ_asymp`'s second summand is essentially `2D₊(v)/v` and
the whole estimate turns on that being small. Same technique as the lower bound: `e^{t²}` is at most
`8/7` times the derivative of `e^{t²}/(2t)` once `t ≥ 2`, so the fundamental theorem bounds the
tail, and the head `[0,2]` is crushed by the `e^{-v²}` in front.

The `8/7` is where the threshold `2` is spent. Taking `t ≥ 1` instead gives a factor `2` and a bound
of `1/v`, which is *not* enough for Corollary 22 — it misses by about 6%. Taking `t ≥ 2` gives
`4/(7v)` and clears it with room.
-/

namespace FKS2Sol

open Real
open FKS2.v2 (dawson)

/-- `D₊` is nonnegative on `[0, ∞)`, which is the only range the conversion evaluates it on. -/
theorem dawson_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ dawson x :=
  mul_nonneg (exp_pos _).le
    (intervalIntegral.integral_nonneg hx fun _ _ ↦ (exp_pos _).le)

theorem continuous_exp_sq : Continuous fun t : ℝ => exp (t ^ 2) :=
  Real.continuous_exp.comp (continuous_pow 2)

theorem dawson_pos {x : ℝ} (hx : 0 < x) : 0 < dawson x :=
  mul_pos (exp_pos _)
    (intervalIntegral.intervalIntegral_pos_of_pos_on
      (continuous_exp_sq.intervalIntegrable 0 x) (fun _ _ ↦ exp_pos _) hx)

/-- **The Dawson differential equation**, `D₊'(x) = 1 - 2x·D₊(x)`.

The paper states it in the form `F'(x) + 2xF(x) = 1` and derives from it that `D₊` has a single
maximum, after which it decreases — the fact its tail estimate needs. Everything here is the
fundamental theorem of calculus applied to a continuous integrand, plus the product rule. -/
theorem hasDerivAt_dawson (x : ℝ) : HasDerivAt dawson (1 - 2 * x * dawson x) x := by
  have hI : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, exp (t ^ 2)) (exp (x ^ 2)) x :=
    (continuous_exp_sq.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hE : HasDerivAt (fun y : ℝ => exp (-y ^ 2)) (exp (-x ^ 2) * -(2 * x)) x := hsq.neg.exp
  have hkey : exp (-x ^ 2) * exp (x ^ 2) = 1 := by rw [← Real.exp_add]; simp
  have hval : exp (-x ^ 2) * -(2 * x) * (∫ t in (0 : ℝ)..x, exp (t ^ 2))
      + exp (-x ^ 2) * exp (x ^ 2) = 1 - 2 * x * dawson x := by
    unfold dawson; rw [hkey]; ring
  exact hval ▸ hE.mul hI

/-- `D₊` is differentiable everywhere, an immediate consequence. -/
theorem differentiable_dawson : Differentiable ℝ dawson :=
  fun x ↦ (hasDerivAt_dawson x).differentiableAt

/-- `∫₀ᵛ e^{t²} dt − e^{v²}/(2v)`, whose positivity is `D₊(v) > 1/(2v)`. -/
noncomputable def dawsonAux (v : ℝ) : ℝ := (∫ t in (0 : ℝ)..v, exp (t ^ 2)) - exp (v ^ 2) / (2 * v)

theorem hasDerivAt_dawsonAux {v : ℝ} (hv : 0 < v) :
    HasDerivAt dawsonAux (exp (v ^ 2) / (2 * v ^ 2)) v := by
  have hI : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, exp (t ^ 2)) (exp (v ^ 2)) v :=
    (continuous_exp_sq.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * v) v := by simpa using hasDerivAt_pow 2 v
  have hE : HasDerivAt (fun y : ℝ => exp (y ^ 2)) (exp (v ^ 2) * (2 * v)) v := hsq.exp
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 v := by
    simpa using (hasDerivAt_id v).const_mul (2 : ℝ)
  have hdiv := hE.div hlin (by positivity : (2 : ℝ) * v ≠ 0)
  refine (hI.sub hdiv).congr_deriv ?_
  field_simp
  ring

theorem integral_exp_sq_one_gt : exp 1 / 2 < ∫ t in (0 : ℝ)..1, exp (t ^ 2) := by
  have hcpoly : Continuous fun t : ℝ => 1 + t ^ 2 + t ^ 4 / 2 := by fun_prop
  have hpoly : (∫ t in (0 : ℝ)..1, (1 + t ^ 2 + t ^ 4 / 2)) = 43 / 30 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => s + s ^ 3 / 3 + s ^ 5 / 10) (1 + t ^ 2 + t ^ 4 / 2) t := by
      intro t _
      have h3 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
        refine ((hasDerivAt_pow 3 t).div_const 3).congr_deriv ?_
        norm_num
      have h5 : HasDerivAt (fun s : ℝ => s ^ 5 / 10) (t ^ 4 / 2) t := by
        refine ((hasDerivAt_pow 5 t).div_const 10).congr_deriv ?_
        norm_num
        ring
      exact ((hasDerivAt_id t).add h3).add h5
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hcpoly.intervalIntegrable _ _)]
    norm_num
  have hmono : (∫ t in (0 : ℝ)..1, (1 + t ^ 2 + t ^ 4 / 2)) ≤ ∫ t in (0 : ℝ)..1, exp (t ^ 2) := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hcpoly.intervalIntegrable _ _)
      (continuous_exp_sq.intervalIntegrable _ _) fun t _ ↦ ?_
    have := Real.quadratic_le_exp_of_nonneg (sq_nonneg t)
    calc 1 + t ^ 2 + t ^ 4 / 2 = 1 + t ^ 2 + (t ^ 2) ^ 2 / 2 := by ring
      _ ≤ exp (t ^ 2) := this
  have he : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rw [hpoly] at hmono
  linarith

/-- `D₊(v) > 1/(2v)` for `v ≥ 1`, which is exactly `D₊'(v) < 0`. -/
theorem inv_lt_dawson {v : ℝ} (hv : 1 ≤ v) : 1 / (2 * v) < dawson v := by
  have hvpos : (0 : ℝ) < v := by linarith
  have hmono : StrictMonoOn dawsonAux (Set.Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1)
      (fun y hy ↦ (hasDerivAt_dawsonAux (by simp at hy; linarith)).continuousAt.continuousWithinAt)
      fun y hy ↦ ?_
    rw [interior_Ici] at hy
    have hy0 : (0 : ℝ) < y := by simp at hy; linarith
    rw [(hasDerivAt_dawsonAux hy0).deriv]
    positivity
  have hpos : 0 < dawsonAux v := by
    have h1 : 0 < dawsonAux 1 := by
      have := integral_exp_sq_one_gt
      unfold dawsonAux
      norm_num
      linarith
    rcases eq_or_lt_of_le hv with h | h
    · rw [← h]; exact h1
    · exact lt_trans h1 (hmono (Set.mem_Ici.mpr (le_refl (1:ℝ))) (Set.mem_Ici.mpr hv) h)
  unfold dawsonAux at hpos
  have hexpn : (0 : ℝ) < exp (-v ^ 2) := exp_pos _
  have hcancel : exp (-v ^ 2) * exp (v ^ 2) = 1 := by rw [← Real.exp_add]; simp
  have hstep : exp (-v ^ 2) * (exp (v ^ 2) / (2 * v))
      < exp (-v ^ 2) * ∫ t in (0 : ℝ)..v, exp (t ^ 2) :=
    mul_lt_mul_of_pos_left (by linarith) hexpn
  have hsimp : exp (-v ^ 2) * (exp (v ^ 2) / (2 * v)) = 1 / (2 * v) := by
    rw [← mul_div_assoc, hcancel]
  unfold dawson
  linarith


/-- `D₊` is strictly decreasing on `[1, ∞)` — past its maximum, which is near `0.9241`. -/
theorem dawson_strictAntiOn : StrictAntiOn dawson (Set.Ici 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 1)
    (fun v _ ↦ (hasDerivAt_dawson v).continuousAt.continuousWithinAt) fun v hv ↦ ?_
  rw [interior_Ici] at hv
  have hv1 : (1 : ℝ) < v := hv
  rw [(hasDerivAt_dawson v).deriv]
  have h2v : (0 : ℝ) < 2 * v := by linarith
  have hkey := (div_lt_iff₀ h2v).mp (inv_lt_dawson hv1.le)
  nlinarith [hkey]

/-- The combination Theorem 3 needs: `D₊(s − c)/s` is antitone once `s ≥ 1 + c`.

Both factors fall — `D₊` because `s − c ≥ 1` puts it past its maximum, and `1/s` because `s` grows.
**This is where the paper's threshold `x₁ ≥ exp((1 + C/(2√R))²)` comes from**: the `1` is exactly
what is needed to clear the Dawson maximum. -/
theorem dawson_shift_div_antitoneOn {c : ℝ} (hc : 0 ≤ c) {s₁ s : ℝ}
    (h1 : 1 + c ≤ s₁) (h : s₁ ≤ s) :
    dawson (s - c) / s ≤ dawson (s₁ - c) / s₁ := by
  have hs₁ : (0 : ℝ) < s₁ := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hmem₁ : s₁ - c ∈ Set.Ici (1 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have hmem : s - c ∈ Set.Ici (1 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have hnum : dawson (s - c) ≤ dawson (s₁ - c) := by
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · exact (dawson_strictAntiOn hmem₁ hmem (by linarith)).le
  have hpos : 0 ≤ dawson (s - c) := dawson_nonneg (by linarith)
  gcongr
  exact dawson_nonneg (by linarith)

/-- `∫₂ᵛ e^{t²} dt ≤ 4e^{v²}/(7v)`.

`d/dt (e^{t²}/(2t)) = e^{t²}(1 - 1/(2t²))`, and for `t ≥ 2` the bracket is at least `7/8`, so the
integrand is at most `8/7` times a derivative and the fundamental theorem does the rest. -/
theorem integral_exp_sq_tail_le {v : ℝ} (hv : 2 ≤ v) :
    (∫ t in (2 : ℝ)..v, exp (t ^ 2)) ≤ 4 * exp (v ^ 2) / (7 * v) := by
  have hvpos : (0 : ℝ) < v := by linarith
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) v,
      HasDerivAt (fun s : ℝ => exp (s ^ 2) / (2 * s)) (exp (t ^ 2) * (1 - 1 / (2 * t ^ 2))) t := by
    intro t ht
    rw [Set.uIcc_of_le hv] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have htne : t ≠ 0 := by linarith
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
    have hE : HasDerivAt (fun s : ℝ => exp (s ^ 2)) (exp (t ^ 2) * (2 * t)) t := hsq.exp
    have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    refine (hE.div hlin (by positivity)).congr_deriv ?_
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => exp (t ^ 2) * (1 - 1 / (2 * t ^ 2))) (Set.uIcc 2 v) := by
    rw [Set.uIcc_of_le hv]
    intro t ht
    have htne : t ≠ 0 := by have := ht.1; linarith
    have hne2 : (2 : ℝ) * t ^ 2 ≠ 0 := by positivity
    exact (((Real.continuous_exp.comp (continuous_pow 2)).continuousAt).mul
      ((continuousAt_const.sub (continuousAt_const.div
        (continuousAt_const.mul ((continuousAt_id).pow 2)) hne2)))).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (2 : ℝ) v,
      exp (t ^ 2) ≤ 8 / 7 * (exp (t ^ 2) * (1 - 1 / (2 * t ^ 2))) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have hb : (7 : ℝ) / 8 ≤ 1 - 1 / (2 * t ^ 2) := by
      have h4 : (4 : ℝ) ≤ t ^ 2 := by nlinarith
      have : 1 / (2 * t ^ 2) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    nlinarith [exp_pos (t ^ 2), hb]
  have hmono : (∫ t in (2 : ℝ)..v, exp (t ^ 2))
      ≤ ∫ t in (2 : ℝ)..v, 8 / 7 * (exp (t ^ 2) * (1 - 1 / (2 * t ^ 2))) :=
    intervalIntegral.integral_mono_on hv (continuous_exp_sq.intervalIntegrable _ _)
      ((continuousOn_const.mul hcont).intervalIntegrable) hpt
  rw [intervalIntegral.integral_const_mul, hFTC] at hmono
  have hF2 : (0 : ℝ) ≤ exp ((2 : ℝ) ^ 2) / (2 * 2) := by positivity
  have hid : 8 / 7 * (exp (v ^ 2) / (2 * v)) = 4 * exp (v ^ 2) / (7 * v) := by
    field_simp
    ring
  linarith [hmono, hF2, hid]

/-- `D₊(v) ≤ 2e^{4-v²} + 4/(7v)` for `v ≥ 2`, the companion upper bound to `inv_lt_dawson`. -/
theorem dawson_le {v : ℝ} (hv : 2 ≤ v) : dawson v ≤ 2 * exp (4 - v ^ 2) + 4 / (7 * v) := by
  have hvpos : (0 : ℝ) < v := by linarith
  have hsplit : (∫ t in (0 : ℝ)..v, exp (t ^ 2))
      = (∫ t in (0 : ℝ)..(2 : ℝ), exp (t ^ 2)) + ∫ t in (2 : ℝ)..v, exp (t ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (continuous_exp_sq.intervalIntegrable _ _) (continuous_exp_sq.intervalIntegrable _ _)).symm
  have hhead : (∫ t in (0 : ℝ)..(2 : ℝ), exp (t ^ 2)) ≤ 2 * exp 4 := by
    have hb : ∀ t ∈ Set.Icc (0 : ℝ) 2, exp (t ^ 2) ≤ exp 4 := by
      intro t ht
      exact exp_le_exp.mpr (by nlinarith [ht.1, ht.2])
    have := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 2)
      (continuous_exp_sq.intervalIntegrable _ _) (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _) hb
    simpa using this
  have htail := integral_exp_sq_tail_le hv
  have hexp : (0 : ℝ) < exp (-v ^ 2) := exp_pos _
  unfold dawson
  rw [hsplit, mul_add]
  have h1 : exp (-v ^ 2) * (∫ t in (0 : ℝ)..(2 : ℝ), exp (t ^ 2)) ≤ 2 * exp (4 - v ^ 2) := by
    have := mul_le_mul_of_nonneg_left hhead hexp.le
    calc exp (-v ^ 2) * (∫ t in (0 : ℝ)..(2 : ℝ), exp (t ^ 2))
        ≤ exp (-v ^ 2) * (2 * exp 4) := this
      _ = 2 * exp (4 - v ^ 2) := by rw [show (4 : ℝ) - v ^ 2 = 4 + -v ^ 2 by ring, Real.exp_add]; ring
  have h2 : exp (-v ^ 2) * (∫ t in (2 : ℝ)..v, exp (t ^ 2)) ≤ 4 / (7 * v) := by
    have := mul_le_mul_of_nonneg_left htail hexp.le
    have hcancel : exp (-v ^ 2) * exp (v ^ 2) = 1 := by rw [← Real.exp_add]; simp
    have hc : exp (-v ^ 2) * (4 * exp (v ^ 2) / (7 * v)) = 4 / (7 * v) := by
      rw [show exp (-v ^ 2) * (4 * exp (v ^ 2) / (7 * v))
            = (exp (-v ^ 2) * exp (v ^ 2)) * (4 / (7 * v)) by ring, hcancel, one_mul]
    linarith [hc ▸ this]
  linarith

end FKS2Sol
