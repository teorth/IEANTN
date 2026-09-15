/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section7Tritura
import Section7Zeros

/-!
# Section 7: `lem:adar`

The sum over zeros with `t₀ < γ ≤ T` of `|ω⁺_{T,σ}(ρ) + ξ θ_{T,1}(ρ) i|`, under RH up to `T`.
Each term is compared with `φ(γ) = √(F(γ/T)² + (1 - γ/T)²)` by `cor:thonny`; `∑ φ(γ)` is turned into
an integral by `lem:Lehmanmodern`, and the integral is `prop:tritura`.
-/

open Real MeasureTheory Set

namespace CH2Section7A

open CH2Section7 CH2Section7T

/-! ### `F` is decreasing, with an explicit derivative -/

theorem hasDerivAt_Fweight {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt Fweight (-Real.cot (Real.pi * u) - (1 - u) * (Real.pi / Real.sin (Real.pi * u) ^ 2)) u := by
  have hs := sin_pi_ne_zero h0 h1
  have hπu : HasDerivAt (fun v : ℝ ↦ Real.pi * v) Real.pi u := by
    simpa using (hasDerivAt_id u).const_mul Real.pi
  have hcot : HasDerivAt (fun v ↦ Real.cot (Real.pi * v))
      (-(1 / Real.sin (Real.pi * u) ^ 2) * Real.pi) u := (hasDerivAt_cot hs).comp u hπu
  have h := (hasDerivAt_const u (1 / Real.pi)).add
    (((hasDerivAt_id u).const_sub 1).mul hcot)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v ↦ ?_)).congr_deriv ?_
  · simp [Fweight_eq]
  · simp only [id]; field_simp; ring

theorem deriv_Fweight_nonpos {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    -Real.cot (Real.pi * u) - (1 - u) * (Real.pi / Real.sin (Real.pi * u) ^ 2) ≤ 0 := by
  have hπ := Real.pi_pos
  set x := Real.pi * u with hx
  have hx0 : 0 < x := by positivity
  have hxπ : x < Real.pi := by nlinarith
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
  have hsin2 : Real.sin (2 * x) ≥ -(2 * Real.pi - 2 * x) := by
    have h := Real.sin_le (by linarith : 0 ≤ 2 * Real.pi - 2 * x)
    rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi] at h
    linarith
  have e : -Real.cot x - (1 - u) * (Real.pi / Real.sin x ^ 2)
      = -(Real.sin x * Real.cos x + (Real.pi - x)) / Real.sin x ^ 2 := by
    rw [Real.cot_eq_cos_div_sin, hx]; field_simp; ring
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  rw [Real.sin_two_mul] at hsin2
  linarith

/-! ### The comparison weight `φ(t) = √(F(t/T)² + (1 - t/T)²)` -/

noncomputable def phiW (T t : ℝ) : ℝ := Real.sqrt (Fweight (t / T) ^ 2 + (1 - t / T) ^ 2)

noncomputable def dF (u : ℝ) : ℝ :=
  -Real.cot (Real.pi * u) - (1 - u) * (Real.pi / Real.sin (Real.pi * u) ^ 2)

noncomputable def phiW' (T t : ℝ) : ℝ :=
  (2 * Fweight (t / T) * dF (t / T) / T - 2 * (1 - t / T) / T) / (2 * phiW T t)

theorem phiW_pos {T t : ℝ} (hT : 0 < T) (htT : t < T) : 0 < phiW T t := by
  unfold phiW
  apply Real.sqrt_pos.mpr
  have : 0 < 1 - t / T := by rw [sub_pos, div_lt_one hT]; exact htT
  positivity

theorem hasDerivAt_phiW {T t : ℝ} (hT : 0 < T) (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (phiW T) (phiW' T t) t := by
  have hu0 : 0 < t / T := div_pos ht0 hT
  have hu1 : t / T < 1 := (div_lt_one hT).mpr htT
  have hdiv : HasDerivAt (fun s : ℝ ↦ s / T) (1 / T) t := by
    simpa using (hasDerivAt_id t).div_const T
  have hFw : HasDerivAt Fweight (dF (t / T)) (t / T) := hasDerivAt_Fweight hu0 hu1
  have hF := hFw.comp t hdiv
  have hQ : HasDerivAt (fun s ↦ Fweight (s / T) ^ 2 + (1 - s / T) ^ 2)
      (2 * Fweight (t / T) * dF (t / T) / T - 2 * (1 - t / T) / T) t := by
    refine ((hF.pow 2).add ((hdiv.const_sub 1).pow 2)).congr_deriv ?_
    simp only [Function.comp_apply]
    push_cast; ring
  have hpos : 0 < Fweight (t / T) ^ 2 + (1 - t / T) ^ 2 := by
    have : 0 < 1 - t / T := by linarith
    positivity
  exact hQ.sqrt hpos.ne'

theorem phiW'_nonpos {T t : ℝ} (hT : 0 < T) (ht0 : 0 < t) (htT : t < T) : phiW' T t ≤ 0 := by
  have hu0 : 0 < t / T := div_pos ht0 hT
  have hu1 : t / T < 1 := (div_lt_one hT).mpr htT
  have hF := Fweight_pos hu0 hu1
  have hdF := deriv_Fweight_nonpos hu0 hu1
  have hp := phiW_pos hT htT
  unfold phiW'
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have h1 : 2 * Fweight (t / T) * dF (t / T) / T ≤ 0 := by
    unfold dF
    apply div_nonpos_of_nonpos_of_nonneg _ hT.le
    nlinarith
  have h2 : 0 ≤ 2 * (1 - t / T) / T := by
    apply div_nonneg _ hT.le; linarith
  linarith

theorem continuousOn_phiW' {T a b : ℝ} (hT : 0 < T) (ha : 0 < a) (hbT : b < T) :
    ContinuousOn (phiW' T) (Set.Icc a b) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have htT : t < T := by linarith [ht.2]
  have hu0 : 0 < t / T := div_pos ht0 hT
  have hu1 : t / T < 1 := (div_lt_one hT).mpr htT
  refine ContinuousAt.continuousWithinAt ?_
  have hs := sin_pi_ne_zero hu0 hu1
  have hcont_div : ContinuousAt (fun s : ℝ ↦ s / T) t := by fun_prop
  have hFc : ContinuousAt (fun s ↦ Fweight (s / T)) t :=
    ((continuousOn_Fweight (a := t / T / 2) (b := (t / T + 1) / 2) (by positivity)
      (by linarith)).continuousAt (Icc_mem_nhds (by linarith) (by linarith))).comp hcont_div
  have hcotc : ContinuousAt (fun s : ℝ ↦ Real.cot (Real.pi * (s / T))) t := by
    simp only [Real.cot_eq_cos_div_sin]
    exact (by fun_prop : ContinuousAt (fun s : ℝ ↦ Real.cos (Real.pi * (s / T))) t).div
      (by fun_prop) hs
  have hdFc : ContinuousAt (fun s ↦ dF (s / T)) t := by
    unfold dF
    exact hcotc.neg.sub (((continuousAt_const.sub hcont_div)).mul
      (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 hs)))
  have hphic : ContinuousAt (phiW T) t := (hasDerivAt_phiW hT ht0 htT).continuousAt
  unfold phiW'
  exact ((((continuousAt_const.mul hFc).mul hdFc).div_const T).sub
    (((continuousAt_const.mul (continuousAt_const.sub hcont_div))).div_const T)).div
    (continuousAt_const.mul hphic) (by have := phiW_pos hT htT; positivity)

end CH2Section7A
