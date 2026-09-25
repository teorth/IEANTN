/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import ZetaInstance
import Section5Neg

/-!
# Proposition 5.2 at `A = -ζ'/ζ`, for `λ < 0`

`prop_5_2_zeta` instantiates `prop_5_2` at `F = -ζ'/ζ` with its pole removed, for `λ > 0`. This file
does the same for `λ < 0`, which is the sign Corollary 1.2 needs.

The boundedness hypotheses on `F` do not involve `λ` and are reused. What changes is the pole
bookkeeping: for `λ < 0` the weights have poles at `s = σ + ikT` inside `R`, so

* `hsimple_circ` needs `F` to be *analytic* at those points, not merely to have simple poles —
  at `s = σ` because `ζ(σ) ≠ 0` (a hypothesis, `ζ` has no real zeros in `[0,1)`), and at `σ ± iT`
  because `T` is not a zero ordinate;
* `hsimple` and `hfin` see `σ ± iT` on the edges of `R \ R_C`, where `Φ_λ` has the removable
  singularities handled in `Section5Neg`.
-/

open Complex Filter Topology

namespace CH2ZetaInstance

/-! ### The weights have at most simple poles -/

theorem Phi_circ_order_ge (ν ε : ℝ) (hν : 0 < ν) (z : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (CH2.Phi_circ ν ε) z := by
  by_cases h : meromorphicOrderAt (CH2.Phi_circ ν ε) z < 0
  · obtain ⟨n, hn⟩ := (CH2.Phi_circ.poles ν ε hν z).mp h
    rw [(CH2.Phi_circ.poles_simple ν ε hν z).mpr ⟨n, hn⟩]
    simp
  · push_neg at h
    exact le_trans (by decide) h

theorem Phi_star_order_ge (ν ε : ℝ) (hν : 0 < ν) (z : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (CH2.Phi_star ν ε) z := by
  by_cases h : meromorphicOrderAt (CH2.Phi_star ν ε) z < 0
  · obtain ⟨n, hn, hz⟩ := (CH2.Phi_star.poles ν ε hν z).mp h
    rw [(CH2.Phi_star.poles_simple ν ε hν z).mpr ⟨n, hn, hz⟩]
    simp
  · push_neg at h
    exact le_trans (by decide) h

theorem hasDerivAt_mul_zOf (l : CH2.LadderParams) (c s : ℂ) :
    HasDerivAt (fun w ↦ c * l.zOf w) (c / (I * (l.T : ℂ))) s := by
  have h := (((hasDerivAt_id s).sub_const 1).div_const (I * (l.T : ℂ))).const_mul c
  simpa [CH2.LadderParams.zOf, div_eq_mul_inv] using h

theorem order_Phi_circ_zOf_ge (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam ≠ 0) (s : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun w ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)) s := by
  have hν : 0 < |lam| := abs_pos.mpr hlam
  have hT : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr l.hT.ne'
  have hsg : ((Real.sign lam : ℝ) : ℂ) ≠ 0 := by
    rcases lt_or_gt_of_ne hlam with h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  have hd := hasDerivAt_mul_zOf l (Real.sign lam : ℂ) s
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := CH2.Phi_circ |lam| ε)
    (g := fun w ↦ (Real.sign lam : ℂ) * l.zOf w) (x := s) (l.analyticAt_zOf _ s)
    (by rw [hd.deriv]; exact div_ne_zero hsg (mul_ne_zero I_ne_zero hT))
  have : (fun w ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w))
      = CH2.Phi_circ |lam| ε ∘ (fun w ↦ (Real.sign lam : ℂ) * l.zOf w) := rfl
  rw [this, hcomp]
  exact Phi_circ_order_ge |lam| ε hν _

/-- A weight pole `σ + ikT` inside `R` is `σ` itself or one of `σ ± iT`. -/
theorem weight_pole_cases (l : CH2.LadderParams) {lam : ℝ} {z : ℂ} (hzT : |z.im| ≤ l.T)
    (hav : ¬ l.AvoidsWeightPoles lam z) :
    z = ((l.sigmaOf lam : ℝ) : ℂ) ∨ |z.im| = l.T := by
  simp only [CH2.LadderParams.AvoidsWeightPoles, not_forall, not_not] at hav
  obtain ⟨k, hk⟩ := hav
  have hT := l.hT
  have him : z.im = (k : ℝ) * l.T := by rw [hk]; simp
  by_cases hk0 : k = 0
  · left
    rw [hk, hk0]
    simp
  · right
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    rw [him, abs_mul, abs_of_pos hT] at hzT ⊢
    nlinarith

/-- **`hsimple_circ` for `λ < 0`.** -/
theorem hasSimplePolesOn_circ_ladder_neg (l : CH2.LadderParams) {lam ε x : ℝ}
    (hlam : lam < 0) (hx : 0 < x)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hσζ : riemannZeta ((l.sigmaOf lam : ℝ) : ℂ) ≠ 0) :
    HasSimplePolesOn
      (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.R := by
  intro z hz
  have hzre : z.re ≤ 1 := hz.1
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  set φ : ℂ → ℂ := fun w ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w) with hφ
  have hsimp : (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)
      = (φ * F) * (fun s : ℂ ↦ (x : ℂ) ^ s) := by
    funext s; simp [hφ]
  rw [hsimp]
  have hφm : MeromorphicAt φ z :=
    (CH2.Phi_circ.meromorphic |lam| ε _).comp_analyticAt (l.analyticAt_zOf _ z)
  have hpow : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ w) z := analyticAt_const_cpow hx z
  have hpowne : ((x : ℂ) ^ z) ≠ 0 := by simp [hxc]
  have hFm : MeromorphicAt F z := meromorphicOn_F z (Set.mem_univ z)
  rw [meromorphicOrderAt_mul (hφm.mul hFm) hpow.meromorphicAt, meromorphicOrderAt_mul hφm hFm]
  have h3 : meromorphicOrderAt (fun w : ℂ ↦ (x : ℂ) ^ w) z = 0 := by
    rw [hpow.meromorphicOrderAt_eq, hpow.analyticOrderAt_eq_zero.mpr hpowne]
    simp
  rw [h3, add_zero]
  by_cases hav : l.AvoidsWeightPoles lam z
  · have h1 : (0 : WithTop ℤ) ≤ meromorphicOrderAt φ z :=
      meromorphicOrderAt_nonneg_of_analyticAt (l.analyticAt_Phi_circ_neg hlam hav)
    have h2 : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F z :=
      hasSimplePolesOn_F_univ z (Set.mem_univ z)
    calc ((-1 : ℤ) : WithTop ℤ) = 0 + ((-1 : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ meromorphicOrderAt φ z + meromorphicOrderAt F z := add_le_add h1 h2
  · have hζ : riemannZeta z ≠ 0 := by
      rcases weight_pole_cases l hz.2 hav with h | h
      · rw [h]; exact hσζ
      · exact fun hc ↦ hTfree z hc h
    have hz1 : z ≠ 1 := by
      intro h
      have hre : z.re = l.sigmaOf lam := by
        simp only [CH2.LadderParams.AvoidsWeightPoles, not_forall, not_not] at hav
        obtain ⟨k, hk⟩ := hav
        rw [hk]; simp
      rw [h, Complex.one_re] at hre
      exact (l.sigmaOf_lt_one hlam).ne' hre
    have h1 : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt φ z :=
      order_Phi_circ_zOf_ge l hlam.ne z
    have h2 : (0 : WithTop ℤ) ≤ meromorphicOrderAt F z :=
      meromorphicOrderAt_nonneg_of_analyticAt (analyticAt_F_of_zeta_ne_zero hz1 hζ)
    calc ((-1 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + 0 := (add_zero _).symm
      _ ≤ meromorphicOrderAt φ z + meromorphicOrderAt F z := add_le_add h1 h2

/-- The order of the `λ < 0` integrand off the real axis and away from weight poles splits as
`(weight) + (order of F)`, as in `meromorphicOrderAt_integrand`. -/
theorem meromorphicOrderAt_integrand_neg (l : CH2.LadderParams) {lam ε x : ℝ}
    (hlam : lam < 0) (hx : 0 < x) {z : ℂ} (him : z.im ≠ 0) (hav : l.AvoidsWeightPoles lam z) :
    ∃ o : WithTop ℤ, 0 ≤ o ∧
      meromorphicOrderAt (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z
        = o + meromorphicOrderAt F z := by
  have hT : 0 < l.T := l.hT
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsign : 0 < z.im ∨ z.im < 0 := (lt_or_gt_of_ne him).symm
  set τ : ℂ := if 0 < z.im then 1 else -1 with hτ_def
  have hlocal : ∀ᶠ w in nhds z, CH2.Phi_lambda lam ε (l.zOf w)
      = CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)
        + ((Real.sign lam : ℂ) * τ) * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf w) := by
    have hopen : ∀ᶠ w in nhds z, (0 < z.im → 0 < w.im) ∧ (z.im < 0 → w.im < 0) := by
      rcases hsign with h | h
      · filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds h] with w hw
        exact ⟨fun _ ↦ hw, fun hc ↦ absurd h (asymm hc)⟩
      · filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds h] with w hw
        exact ⟨fun hc ↦ absurd h (asymm hc), fun _ ↦ hw⟩
    filter_upwards [hopen] with w hw
    have hre : (l.zOf w).re = w.im / l.T := re_zOf l w
    simp only [CH2.Phi_lambda, hre, hτ_def]
    rcases hsign with h | h
    · have hwim : 0 < w.im := hw.1 h
      rw [if_pos h, Real.sign_of_pos (div_pos hwim hT)]
      push_cast
      ring
    · have hwim : w.im < 0 := hw.2 h
      rw [if_neg (asymm h), Real.sign_of_neg (div_neg_of_neg_of_pos hwim hT)]
      push_cast
      ring
  have hPhi : AnalyticAt ℂ
      (fun w ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)
        + ((Real.sign lam : ℂ) * τ) * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf w)) z :=
    (l.analyticAt_Phi_circ_neg hlam hav).add
      (analyticAt_const.mul (l.analyticAt_Phi_star_neg hlam hav))
  have hpow : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ w) z := analyticAt_const_cpow hx z
  have hpowne : ((x : ℂ) ^ z) ≠ 0 := by simp [hxc]
  have hFm : MeromorphicAt F z := meromorphicOn_F z (Set.mem_univ z)
  have hcongr : meromorphicOrderAt (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z
      = meromorphicOrderAt
          (((fun w ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)
            + ((Real.sign lam : ℂ) * τ) * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf w)) * F)
            * (fun s : ℂ ↦ (x : ℂ) ^ s)) z := by
    refine meromorphicOrderAt_congr ?_
    filter_upwards [nhdsWithin_le_nhds hlocal] with w hw
    simp only [Pi.mul_apply, hw]
  have h3 : meromorphicOrderAt (fun w : ℂ ↦ (x : ℂ) ^ w) z = 0 := by
    rw [hpow.meromorphicOrderAt_eq, hpow.analyticOrderAt_eq_zero.mpr hpowne]
    simp
  refine ⟨meromorphicOrderAt
      (fun w ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)
        + ((Real.sign lam : ℂ) * τ) * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf w)) z,
    meromorphicOrderAt_nonneg_of_analyticAt hPhi, ?_⟩
  rw [hcongr, meromorphicOrderAt_mul (hPhi.meromorphicAt.mul hFm) hpow.meromorphicAt,
    meromorphicOrderAt_mul hPhi.meromorphicAt hFm, h3, add_zero]

/-- On `R \ R_C` the only weight poles are the two edge points `σ ± iT`. -/
theorem avoidsWeightPoles_of_band (l : CH2.LadderParams) {lam : ℝ} {z : ℂ}
    (hzT : |z.im| ≤ l.T) (hdlt : l.δ < |z.im|)
    (htop : z ≠ ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I)
    (hbot : z ≠ ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I) :
    l.AvoidsWeightPoles lam z := by
  by_contra hav
  have hre : z.re = l.sigmaOf lam := by
    simp only [CH2.LadderParams.AvoidsWeightPoles, not_forall, not_not] at hav
    obtain ⟨k, hk⟩ := hav
    rw [hk]; simp
  rcases weight_pole_cases l hzT hav with h | h
  · have : z.im = 0 := by rw [h]; simp
    rw [this, abs_zero] at hdlt
    exact absurd l.hδ.1 (not_lt.mpr hdlt.le)
  · rcases (abs_eq l.hT.le).mp h with hi | hi
    · exact htop (Complex.ext (by simp [hre]) (by simp [hi]))
    · exact hbot (Complex.ext (by simp [hre]) (by simp [hi]))

/-- **`hfin` for `λ < 0`**: the zeros in the band, plus at most the two edge points. -/
theorem finite_poles_ladder_neg (l : CH2.LadderParams) {lam ε x : ℝ}
    (hlam : lam < 0) (hx : 0 < x) :
    {z ∈ l.R \ l.RC |
      meromorphicOrderAt (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z
        < 0}.Finite := by
  have hT : 0 < l.T := l.hT
  have hd0 : 0 < l.δ := l.hδ.1
  have h1K : (1 : ℂ) ∉ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ l.δ ≤ |z.im| ∧ |z.im| ≤ l.T} := by
    intro h
    have hm := h.2.2.1
    simp only [Complex.one_im, abs_zero] at hm
    linarith
  refine Set.Finite.subset
    ((finite_zeros_riemannZeta_of_isCompact (isCompact_band l.δ l.T) h1K).union
      (Set.toFinite ({((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I,
        ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I} : Set ℂ))) ?_
  rintro z ⟨⟨hzR, hzRC⟩, hord⟩
  have hzre : z.re ≤ 1 := hzR.1
  have hzT : |z.im| ≤ l.T := hzR.2
  have hdlt : l.δ < |z.im| := by
    by_contra hc
    exact hzRC ⟨hzre, not_lt.mp hc⟩
  by_cases htop : z = ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I
  · right; rw [htop]; simp
  by_cases hbot : z = ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I
  · right; rw [hbot]; simp
  left
  have him : z.im ≠ 0 := by
    intro h
    rw [h] at hdlt
    simp only [abs_zero] at hdlt
    linarith
  have hav := avoidsWeightPoles_of_band l hzT hdlt htop hbot
  obtain ⟨o, ho, heq⟩ := meromorphicOrderAt_integrand_neg l (ε := ε) hlam hx him hav
  rw [heq] at hord
  have hFord : meromorphicOrderAt F z < 0 := by
    by_contra hc
    push_neg at hc
    refine absurd hord (not_lt.mpr ?_)
    calc (0 : WithTop ℤ) = 0 + 0 := (add_zero 0).symm
      _ ≤ o + meromorphicOrderAt F z := by gcongr
  have hz1zero : riemannZeta₁ z = 0 := by
    by_contra hc
    exact absurd hFord (not_lt.mpr (meromorphicOrderAt_nonneg_of_analyticAt (analyticAt_F hc)))
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at him
    simp only [Complex.one_im] at him
    exact him rfl
  have hzeta : riemannZeta z = 0 := (riemannZeta_eq_zero_iff_riemannZeta₁ hz1).mpr hz1zero
  obtain ⟨hre0, hre1⟩ := re_mem_Icc_of_riemannZeta_eq_zero hzeta him
  exact ⟨⟨hre0, hre1, hdlt.le, hzT⟩, hzeta⟩

/-- **`hsimple` for `λ < 0`**: at `σ ± iT` the integrand is regular (the removable singularity,
with `F` analytic because `T` is not a zero ordinate); elsewhere the order splits as before. -/
theorem hasSimplePolesOn_lambda_ladder_neg (l : CH2.LadderParams) {lam ε x : ℝ}
    (hlam : lam < 0) (hx : 0 < x)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T) :
    HasSimplePolesOn (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s)
      (l.Rpos ∪ l.RposBar) := by
  have hd0 : 0 < l.δ := l.hδ.1
  have hT := l.hT
  intro z hz
  obtain ⟨hzre, hzT, hdle⟩ : z.re ≤ 1 ∧ |z.im| ≤ l.T ∧ l.δ ≤ |z.im| := by
    rcases hz with h | h
    · refine ⟨h.1, ?_, ?_⟩
      · rw [abs_of_pos (lt_of_lt_of_le hd0 h.2.1)]; exact h.2.2
      · rw [abs_of_pos (lt_of_lt_of_le hd0 h.2.1)]; exact h.2.1
    · have hneg : z.im < 0 := lt_of_le_of_lt h.2.2 (neg_lt_zero.mpr hd0)
      refine ⟨h.1, ?_, ?_⟩
      · rw [abs_of_neg hneg]; linarith [h.2.1]
      · rw [abs_of_neg hneg]; linarith [h.2.2]
  have him : z.im ≠ 0 := by
    intro h; rw [h, abs_zero] at hdle; linarith
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hheq : (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s)
      = (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * (F s * (x : ℂ) ^ s)) := by
    funext s; ring
  -- at an edge point, `F` is analytic and the removable singularity gives order `≥ 0`
  have hedge : ∀ z₀ : ℂ, |z₀.im| = l.T → z₀.re < 1 →
      MeromorphicAt (fun s ↦ F s * (x : ℂ) ^ s) z₀ ∧
        0 ≤ meromorphicOrderAt (fun s ↦ F s * (x : ℂ) ^ s) z₀ := by
    intro z₀ hz₀ hz₀re
    have hζ : riemannZeta z₀ ≠ 0 := fun hc ↦ hTfree z₀ hc hz₀
    have hz1 : z₀ ≠ 1 := by intro h; rw [h, Complex.one_re] at hz₀re; exact lt_irrefl _ hz₀re
    have hFa := analyticAt_F_of_zeta_ne_zero hz1 hζ
    have hpow : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ w) z₀ := analyticAt_const_cpow hx z₀
    exact ⟨(hFa.mul hpow).meromorphicAt, meromorphicOrderAt_nonneg_of_analyticAt (hFa.mul hpow)⟩
  have hσ1 := l.sigmaOf_lt_one hlam
  by_cases htop : z = ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I
  · rw [hheq, htop]
    obtain ⟨hm, ho⟩ := hedge (((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I)
      (by simp [abs_of_pos hT]) (by simpa using hσ1)
    exact le_trans (by decide) (l.meromorphicOrderAt_Phi_lambda_mul_top_neg hlam hm ho)
  by_cases hbot : z = ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I
  · rw [hheq, hbot]
    obtain ⟨hm, ho⟩ := hedge (((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I)
      (by simp [abs_of_pos hT]) (by simpa using hσ1)
    exact le_trans (by decide) (l.meromorphicOrderAt_Phi_lambda_mul_bot_neg hlam hm ho)
  have hav : l.AvoidsWeightPoles lam z := by
    by_contra hav
    have hre : z.re = l.sigmaOf lam := by
      simp only [CH2.LadderParams.AvoidsWeightPoles, not_forall, not_not] at hav
      obtain ⟨k, hk⟩ := hav
      rw [hk]; simp
    rcases weight_pole_cases l hzT hav with h | h
    · exact him (by rw [h]; simp)
    · rcases (abs_eq hT.le).mp h with hi | hi
      · exact htop (Complex.ext (by simp [hre]) (by simp [hi]))
      · exact hbot (Complex.ext (by simp [hre]) (by simp [hi]))
  obtain ⟨o, ho, heq⟩ := meromorphicOrderAt_integrand_neg l (ε := ε) hlam hx him hav
  rw [heq]
  have h2 : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F z :=
    hasSimplePolesOn_F_univ z (Set.mem_univ z)
  calc ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F z := h2
    _ = 0 + meromorphicOrderAt F z := (zero_add _).symm
    _ ≤ o + meromorphicOrderAt F z := by gcongr

/-- **Proposition 5.2 at `A = -ζ'/ζ`, for `λ < 0`.**

The extra hypotheses over `prop_5_2_zeta` are `0 ≤ σ`, so that every ladder column `1 - 2n` lies at
least `1` to the left of `σ`, and `ζ(σ) ≠ 0`, so that `F` is analytic at the new pole `s = σ`. -/
theorem prop_5_2_zeta_neg
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    {l : CH2.LadderParams} (hsig : l.σ = sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hdfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {lam ε x₀ x : ℝ} (hlam : lam < 0) (hε : ε = 1 ∨ ε = -1)
    (hσ0 : 0 ≤ l.sigmaOf lam) (hσζ : riemannZeta ((l.sigmaOf lam : ℝ) : ℂ) ≠ 0)
    (hx₀ : 1 < x₀) (hx : x₀ < x) :
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) -
        sumResiduesIn (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) -
        l.sumResiduesLim
          (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)
          l.RC‖ ≤
      (1 / (2 * Real.pi)) *
        ((1 / l.T) *
            ((∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t + l.T * Complex.I)‖ * x ^ (1 - t)) +
              ∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t - l.T * Complex.I)‖ * x ^ (1 - t)) +
          2 * ‖l.intC (fun s ↦ CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s
              * (x : ℂ) ^ s)‖) := by
  have hL : ∀ n, 1 ≤ n → l.σ n ≤ l.sigmaOf lam - 1 := by
    intro n hn
    rw [hsig, sigmaZeta]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact CH2.prop_5_2_neg (fun z _ ↦ meromorphicOn_F z (Set.mem_univ z)) conjSymm_F hlam hε
    one_pos hL hx₀.le
    (isBoundedNoPolesOn_ladder hfe hdig hsig hTfree hdfree hx₀)
    (isBoundedNoPolesOn_ladder_weighted hfe hdig hsig hTfree hdfree hx₀)
    hx
    (finite_poles_ladder_neg l hlam (by linarith))
    (hasSimplePolesOn_lambda_ladder_neg l hlam (by linarith) hTfree)
    (hasSimplePolesOn_circ_ladder_neg l hlam (by linarith) hTfree hσζ)

end CH2ZetaInstance
