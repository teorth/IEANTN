/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section6
import Section7
import IEANTN.Vocabulary.Zeta

/-!
# Section 6: the residues

`svm_bounds` leaves the residue sum of the shifted integrand in `sumResiduesIn`/`sumResiduesLim`
form. This file evaluates the pieces:

* the residue of `F = -ζ'/ζ - 1/(s-1)` at a zero `ρ` of `ζ` is `-m(ρ)`, its multiplicity
  (`tendsto_sub_mul_F`), from a general fact about logarithmic derivatives;
* the trivial zeros are simple (`zetaOrder_trivial`), from the functional equation: the factor
  `cos(πs/2)` has a simple zero at the odd integer `2k + 3` and nothing else in
  `2(2π)^{-s} Γ(s) cos(πs/2) ζ(s)` vanishes there.
-/

open Complex Filter Topology

namespace CH2Section6

/-- **The residue of a logarithmic derivative is the order.** -/
theorem tendsto_sub_mul_logDeriv {f : ℂ → ℂ} {x : ℂ} {n : ℤ} (hf : MeromorphicAt f x)
    (hord : meromorphicOrderAt f x = n) :
    Tendsto (fun z ↦ (z - x) * logDeriv f z) (𝓝[≠] x) (𝓝 (n : ℂ)) := by
  rw [meromorphicOrderAt_eq_int_iff hf] at hord
  obtain ⟨g, hga, hg0, (hg : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z)⟩ := hord
  have hderiv : ∀ᶠ z in 𝓝[≠] x,
      deriv f z = (z - x) ^ (n - 1) * ((n : ℂ) * g z + (z - x) * deriv g z) := by
    filter_upwards [hga.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin, hg.nhdsNE_deriv] with z hgz hmem hz
    have hzx : z - x ≠ 0 := by simpa [sub_eq_zero] using hmem
    calc deriv f z = deriv (fun z ↦ (z - x) ^ n • g z) z := hz
      _ = (z - x) ^ n • deriv g z + deriv ((· ^ n) ∘ (· - x)) z • g z :=
        deriv_fun_smul (by fun_prop (disch := grind)) hgz.differentiableAt
      _ = (z - x) ^ n • deriv g z + (n * (z - x) ^ (n - 1)) • g z := by
        rw [deriv_comp _ (by fun_prop (disch := grind)) (by fun_prop)]
        simp [deriv_zpow]
      _ = (z - x) ^ (n - 1) * ((n : ℂ) * g z + (z - x) * deriv g z) := by
        simp only [smul_eq_mul]
        rw [show (z - x) ^ n = (z - x) ^ (n - 1) * (z - x) by
          rw [← zpow_add_one₀ hzx]; ring_nf]
        ring
  have hlim : Tendsto (fun z ↦ ((n : ℂ) * g z + (z - x) * deriv g z) / g z) (𝓝[≠] x)
      (𝓝 (((n : ℂ) * g x + (x - x) * deriv g x) / g x)) := by
    have hc : ContinuousAt (fun z ↦ ((n : ℂ) * g z + (z - x) * deriv g z) / g z) x :=
      ((continuousAt_const.mul hga.continuousAt).add
        ((continuousAt_id.sub continuousAt_const).mul hga.deriv.continuousAt)).div
        hga.continuousAt hg0
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hval : ((n : ℂ) * g x + (x - x) * deriv g x) / g x = n := by
    rw [sub_self, zero_mul, add_zero]
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hderiv, hg, eventually_mem_nhdsWithin,
    hga.continuousAt.eventually_ne hg0 |>.filter_mono nhdsWithin_le_nhds] with z hdz hfz hmem hgz
  have hzx : z - x ≠ 0 := by simpa [sub_eq_zero] using hmem
  rw [logDeriv_apply, hdz, hfz, smul_eq_mul]
  rw [show (z - x) ^ n = (z - x) ^ (n - 1) * (z - x) by
    rw [← zpow_add_one₀ hzx]; ring_nf]
  have hp : (z - x) ^ (n - 1) ≠ 0 := zpow_ne_zero _ hzx
  field_simp

/-- `ζ₁ = (s-1)ζ` has the same order as `ζ` away from `s = 1`. -/
theorem meromorphicOrderAt_riemannZeta₁_eq {ρ : ℂ} (hρ : ρ ≠ 1) :
    meromorphicOrderAt riemannZeta₁ ρ = meromorphicOrderAt riemannZeta ρ := by
  have hEq : riemannZeta₁ =ᶠ[𝓝[≠] ρ] (fun z ↦ (z - 1) * riemannZeta z) := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
      (show ρ ∈ ({(1 : ℂ)}ᶜ) from hρ))] with z hz
    exact CH2ZetaInstance.riemannZeta₁_eq_mul hz
  rw [meromorphicOrderAt_congr hEq,
    show (fun z ↦ (z - 1) * riemannZeta z) = (fun z ↦ z - 1) * riemannZeta from rfl,
    meromorphicOrderAt_mul (by fun_prop)
      (CH2ZetaInstance.meromorphicOn_riemannZeta ρ (Set.mem_univ ρ))]
  have h1 : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) ρ := by fun_prop
  have h0 : meromorphicOrderAt (fun z : ℂ ↦ z - 1) ρ = 0 := by
    rw [h1.meromorphicOrderAt_eq, h1.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ)]
    simp
  rw [h0, zero_add]

/-- **The residue of `F` at `ρ ≠ 1` is `-m(ρ)`**, `m` the multiplicity of `ρ` as a zero of `ζ`
(`0` if `ζ(ρ) ≠ 0`). -/
theorem tendsto_sub_mul_F {ρ : ℂ} (hρ : ρ ≠ 1) :
    Tendsto (fun z ↦ (z - ρ) * CH2ZetaInstance.F z) (𝓝[≠] ρ)
      (𝓝 (-((IEANTN.zetaOrder ρ : ℤ) : ℂ))) := by
  have hne := CH2ZetaInstance.meromorphicOrderAt_riemannZeta_ne_top ρ
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  have hord : meromorphicOrderAt riemannZeta₁ ρ = n := by
    rw [meromorphicOrderAt_riemannZeta₁_eq hρ, ← hn]
  have hz : IEANTN.zetaOrder ρ = n := by
    rw [IEANTN.zetaOrder, ← hn]
    rfl
  have h := (tendsto_sub_mul_logDeriv (CH2ZetaInstance.analyticAt_riemannZeta₁ ρ).meromorphicAt
    hord).neg
  rw [hz]
  refine h.congr fun z ↦ ?_
  simp [CH2ZetaInstance.F]

/-! ### The trivial zeros are simple -/

/-- A function analytic and nonzero at a point has meromorphic order `0` there. -/
theorem meromorphicOrderAt_eq_zero_of_analytic {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (hx : f x ≠ 0) : meromorphicOrderAt f x = 0 := by
  rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_zero.mpr hx]
  simp

/-- **`ζ` has a simple zero at `-2(k+1)`.**

Through `ζ(1-s) = 2(2π)^{-s} Γ(s) cos(πs/2) ζ(s)` at `s = 2k + 3`: every factor but the cosine is
analytic and nonzero there, and `cos(πs/2)` has a simple zero, its derivative being
`-(π/2) sin(πs/2) = ±π/2`. -/
theorem meromorphicOrderAt_riemannZeta_trivial (k : ℕ) :
    meromorphicOrderAt riemannZeta (-2 * ((k : ℂ) + 1)) = 1 := by
  set s₀ : ℂ := 2 * (k : ℂ) + 3 with hs₀
  have hs₀re : 1 < s₀.re := by
    simp [hs₀]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  -- the functional equation, on a neighbourhood of `s₀`
  have hloc : (fun s ↦ riemannZeta (1 - s)) =ᶠ[𝓝 s₀]
      (fun s ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2)
        * riemannZeta s) := by
    filter_upwards [hopen.mem_nhds hs₀re] with s hs
    have hs' : 1 < s.re := hs
    refine riemannZeta_one_sub (fun n hn ↦ ?_) (fun h ↦ ?_)
    · have : s.re = -(n : ℝ) := by rw [hn]; simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · rw [h] at hs'; simp at hs'
  -- order of the left side
  have hcomp : meromorphicOrderAt (fun s ↦ riemannZeta (1 - s)) s₀
      = meromorphicOrderAt riemannZeta (-2 * ((k : ℂ) + 1)) := by
    have hg : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) s₀ := by fun_prop
    have hd : deriv (fun s : ℂ ↦ 1 - s) s₀ ≠ 0 := by
      rw [deriv_const_sub, deriv_id'']; norm_num
    have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) hg hd
    rw [show (1 : ℂ) - s₀ = -2 * ((k : ℂ) + 1) by rw [hs₀]; ring] at h
    exact h
  -- the factors at `s₀`
  have hΓpole : ∀ m : ℕ, s₀ ≠ -(m : ℂ) := by
    intro m hm
    have : s₀.re = -(m : ℝ) := by rw [hm]; simp
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hΓa : AnalyticAt ℂ Complex.Gamma s₀ := by
    have hΓd : DifferentiableOn ℂ Complex.Gamma {s : ℂ | 1 < s.re} := fun s hs ↦
      (Complex.differentiableAt_Gamma s (fun m hm ↦ by
        have hs' : 1 < s.re := hs
        have : s.re = -(m : ℝ) := by rw [hm]; simp
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith)).differentiableWithinAt
    exact hΓd.analyticOnNhd hopen s₀ hs₀re
  have hΓne : Complex.Gamma s₀ ≠ 0 := Complex.Gamma_ne_zero hΓpole
  have hζa : AnalyticAt ℂ riemannZeta s₀ := by
    have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | 1 < s.re} := fun s hs ↦
      (differentiableAt_riemannZeta (by
        intro h; have hs' : 1 < s.re := hs; rw [h] at hs'; simp at hs')).differentiableWithinAt
    exact hd.analyticOnNhd hopen s₀ hs₀re
  have hζne : riemannZeta s₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs₀re
  have hpowa : AnalyticAt ℂ (fun s : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-s)) s₀ := by
    have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    exact (differentiable_id.neg.const_cpow (Or.inl h2π)).analyticAt s₀
  have hpowne : (2 * (Real.pi : ℂ)) ^ (-s₀) ≠ 0 := by
    have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; have := congrArg Complex.re h; simp [hs₀] at this; linarith [this])).mpr h2π
  have hcosa : AnalyticAt ℂ (fun s : ℂ ↦ Complex.cos (Real.pi * s / 2)) s₀ := by fun_prop
  have hcos0 : Complex.cos (Real.pi * s₀ / 2) = 0 := by
    rw [Complex.cos_eq_zero_iff]
    exact ⟨k + 1, by rw [hs₀]; push_cast; ring⟩
  have hcosd : deriv (fun s : ℂ ↦ Complex.cos (Real.pi * s / 2)) s₀ ≠ 0 := by
    have hd : HasDerivAt (fun s : ℂ ↦ Complex.cos (Real.pi * s / 2))
        (-Complex.sin (Real.pi * s₀ / 2) * (Real.pi / 2)) s₀ := by
      have h1 : HasDerivAt (fun s : ℂ ↦ (Real.pi : ℂ) * s / 2) ((Real.pi : ℂ) / 2) s₀ := by
        simpa using ((hasDerivAt_id s₀).const_mul (Real.pi : ℂ)).div_const 2
      exact (Complex.hasDerivAt_cos _).comp s₀ h1
    rw [hd.deriv]
    have hsin : Complex.sin (Real.pi * s₀ / 2) ≠ 0 := by
      intro h
      have := Complex.sin_sq_add_cos_sq (Real.pi * s₀ / 2)
      rw [h, hcos0] at this
      norm_num at this
    have hπ : (Real.pi : ℂ) / 2 ≠ 0 := by simp [Real.pi_ne_zero]
    exact mul_ne_zero (neg_ne_zero.mpr hsin) hπ
  have hcos1 : meromorphicOrderAt (fun s : ℂ ↦ Complex.cos (Real.pi * s / 2)) s₀ = 1 := by
    rw [hcosa.meromorphicOrderAt_eq, hcosa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hcos0 hcosd]
    rfl
  -- order of the right side
  have hR : meromorphicOrderAt
      (fun s ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2)
        * riemannZeta s) s₀ = 1 := by
    have e : (fun s ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s
        * Complex.cos (Real.pi * s / 2) * riemannZeta s)
        = ((((fun _ : ℂ ↦ (2 : ℂ)) * fun s : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-s)) * Complex.Gamma)
          * fun s : ℂ ↦ Complex.cos (Real.pi * s / 2)) * riemannZeta := by
      funext s; simp [Pi.mul_apply]
    rw [e, meromorphicOrderAt_mul (by fun_prop) hζa.meromorphicAt,
      meromorphicOrderAt_mul (by fun_prop) hcosa.meromorphicAt,
      meromorphicOrderAt_mul (by fun_prop) hΓa.meromorphicAt,
      meromorphicOrderAt_mul analyticAt_const.meromorphicAt hpowa.meromorphicAt,
      meromorphicOrderAt_eq_zero_of_analytic analyticAt_const (by norm_num),
      meromorphicOrderAt_eq_zero_of_analytic hpowa hpowne,
      meromorphicOrderAt_eq_zero_of_analytic hΓa hΓne, hcos1,
      meromorphicOrderAt_eq_zero_of_analytic hζa hζne]
    rfl
  rw [← hcomp, meromorphicOrderAt_congr (hloc.filter_mono nhdsWithin_le_nhds), hR]

theorem zetaOrder_trivial (k : ℕ) : IEANTN.zetaOrder (-2 * ((k : ℂ) + 1)) = 1 := by
  rw [IEANTN.zetaOrder, meromorphicOrderAt_riemannZeta_trivial]
  rfl

/-! ### The residues off the band `R_C` -/

/-- A residue of `g · f`, from the local behaviour of `f` and continuity of `g`. -/
theorem residue_eq_mul_of_tendsto {f g h : ℂ → ℂ} {p c : ℂ} (hg : ContinuousAt g p)
    (hf : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 c))
    (hev : ∀ᶠ s in 𝓝[≠] p, h s = g s * f s) :
    residue h p = g p * c := by
  apply residue_eq_of_tendsto
  have hlim := (hg.tendsto.mono_left nhdsWithin_le_nhds).mul hf
  refine hlim.congr' ?_
  filter_upwards [hev] with s hs
  rw [hs]
  ring

/-- Off the real axis `Φ_λ(z(s))` is locally `Φ^∘ + c Φ^⋆`, the sign factor being constant. -/
theorem Phi_lambda_local (l : CH2.LadderParams) (lam ε : ℝ) {z : ℂ} (him : z.im ≠ 0) :
    ∃ c : ℂ, ∀ᶠ w in 𝓝 z, CH2.Phi_lambda lam ε (l.zOf w)
      = CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)
        + c * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf w) := by
  have hT := l.hT
  rcases lt_or_gt_of_ne him with h | h
  · refine ⟨(Real.sign lam : ℂ) * (-1), ?_⟩
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds h] with w hw
    have hwim : w.im < 0 := hw
    simp only [CH2.Phi_lambda, CH2ZetaInstance.re_zOf,
      Real.sign_of_neg (div_neg_of_neg_of_pos hwim hT)]
    push_cast
    ring
  · refine ⟨(Real.sign lam : ℂ) * 1, ?_⟩
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds h] with w hw
    have hwim : 0 < w.im := hw
    simp only [CH2.Phi_lambda, CH2ZetaInstance.re_zOf, Real.sign_of_pos (div_pos hwim hT)]
    push_cast
    ring

/-- **Every residue in `R \ R_C` is `-m(ρ) Φ_λ(z(ρ)) x^ρ`**, zero away from the zeros of `ζ`
(including at the removable singularities `σ ± iT`). -/
theorem residue_band_neg (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0) (hx : 0 < x)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T) {z : ℂ} (hz : z ∈ l.R \ l.RC) :
    residue (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s) z
      = CH2.Phi_lambda lam ε (l.zOf z) * (x : ℂ) ^ z * (-((IEANTN.zetaOrder z : ℤ) : ℂ)) := by
  obtain ⟨⟨hzre, hzT⟩, hzRC⟩ := hz
  have hdlt : l.δ < |z.im| := by
    by_contra hc
    exact hzRC ⟨hzre, not_lt.mp hc⟩
  have hd0 := l.hδ.1
  have him : z.im ≠ 0 := by
    intro h; rw [h, abs_zero] at hdlt; linarith
  have hz1 : z ≠ 1 := by intro h; rw [h] at him; simp at him
  have hF := tendsto_sub_mul_F hz1
  have hpow : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ w) z :=
    CH2ZetaInstance.analyticAt_const_cpow hx z
  by_cases htop : z = ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I
  · -- the removable singularity: `ζ(z) ≠ 0`, so `m = 0`, and the weight is locally analytic
    have hζ : riemannZeta z ≠ 0 := fun hc ↦ hTfree z hc (by rw [htop]; simp [abs_of_pos l.hT])
    have hm : IEANTN.zetaOrder z = 0 := by
      have hFa := CH2ZetaInstance.analyticAt_riemannZeta hz1
      rw [IEANTN.zetaOrder, meromorphicOrderAt_eq_zero_of_analytic hFa hζ]
      rfl
    rw [hm]
    have hzim : 0 < z.im := by rw [htop]; simp [l.hT]
    have hg : AnalyticAt ℂ (fun w ↦ -CH2.Phi_star |lam| ε (1 - l.zOf w) * (x : ℂ) ^ w) z := by
      have hzA : AnalyticAt ℂ l.zOf z := by simpa using l.analyticAt_zOf 1 z
      refine (((CH2.Phi_star.analyticAt_of_not_pole_nz |lam| ε (1 - l.zOf z) ?_).comp_of_eq
        (analyticAt_const.sub hzA) rfl).neg).mul hpow
      intro n hn heq
      have hL : (1 - l.zOf z).re = 0 := by
        rw [Complex.sub_re, Complex.one_re, l.zOf_re, htop]
        simp [l.hT.ne']
      have heq' : 1 - l.zOf z = ((n : ℝ) : ℂ) + ((-(|lam| / (2 * Real.pi)) : ℝ) : ℂ) * I := by
        rw [heq]; push_cast; ring
      have hre := congrArg Complex.re heq'
      rw [hL] at hre
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, add_zero, mul_one] at hre
      exact hn (by exact_mod_cast hre.symm)
    have hev : ∀ᶠ s in 𝓝[≠] z,
        CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s
          = (-CH2.Phi_star |lam| ε (1 - l.zOf s) * (x : ℂ) ^ s) * CH2ZetaInstance.F s := by
      have hopen : ∀ᶠ w in 𝓝 z, 0 < w.im :=
        (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim
      filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with w hw hw'
      rw [l.Phi_lambda_neg_eq_top hlam hw (by rw [← htop]; exact hw')]
      ring
    rw [residue_eq_mul_of_tendsto hg.continuousAt hF hev]
    simp [hm]
  by_cases hbot : z = ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I
  · have hζ : riemannZeta z ≠ 0 := fun hc ↦ hTfree z hc (by rw [hbot]; simp [abs_of_pos l.hT])
    have hm : IEANTN.zetaOrder z = 0 := by
      have hFa := CH2ZetaInstance.analyticAt_riemannZeta hz1
      rw [IEANTN.zetaOrder, meromorphicOrderAt_eq_zero_of_analytic hFa hζ]
      rfl
    rw [hm]
    have hzim : z.im < 0 := by rw [hbot]; simp [l.hT]
    have hg : AnalyticAt ℂ (fun w ↦ CH2.Phi_star |lam| ε (-1 - l.zOf w) * (x : ℂ) ^ w) z := by
      have hzA : AnalyticAt ℂ l.zOf z := by simpa using l.analyticAt_zOf 1 z
      refine ((CH2.Phi_star.analyticAt_of_not_pole_nz |lam| ε (-1 - l.zOf z) ?_).comp_of_eq
        (analyticAt_const.sub hzA) rfl).mul hpow
      intro n hn heq
      have hL : (-1 - l.zOf z).re = 0 := by
        rw [Complex.sub_re, Complex.neg_re, Complex.one_re, l.zOf_re, hbot]
        simp [l.hT.ne']
      have heq' : -1 - l.zOf z = ((n : ℝ) : ℂ) + ((-(|lam| / (2 * Real.pi)) : ℝ) : ℂ) * I := by
        rw [heq]; push_cast; ring
      have hre := congrArg Complex.re heq'
      rw [hL] at hre
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, add_zero, mul_one] at hre
      exact hn (by exact_mod_cast hre.symm)
    have hev : ∀ᶠ s in 𝓝[≠] z,
        CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s
          = (CH2.Phi_star |lam| ε (-1 - l.zOf s) * (x : ℂ) ^ s) * CH2ZetaInstance.F s := by
      have hopen : ∀ᶠ w in 𝓝 z, w.im < 0 :=
        (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzim
      filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with w hw hw'
      rw [l.Phi_lambda_neg_eq_bot hlam hw (by rw [← hbot]; exact hw')]
      ring
    rw [residue_eq_mul_of_tendsto hg.continuousAt hF hev]
    simp [hm]
  -- a generic point of the band: the weight is locally analytic
  have hav := CH2ZetaInstance.avoidsWeightPoles_of_band l hzT hdlt htop hbot
  obtain ⟨c, hc⟩ := Phi_lambda_local l lam ε him
  have hg : AnalyticAt ℂ (fun w ↦ (CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)
      + c * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf w)) * (x : ℂ) ^ w) z :=
    ((l.analyticAt_Phi_circ_neg hlam hav).add
      (analyticAt_const.mul (l.analyticAt_Phi_star_neg hlam hav))).mul hpow
  have hev : ∀ᶠ s in 𝓝[≠] z,
      CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s
        = ((CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)
          + c * CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) * (x : ℂ) ^ s)
          * CH2ZetaInstance.F s := by
    filter_upwards [nhdsWithin_le_nhds hc] with w hw
    rw [hw]
    ring
  rw [residue_eq_mul_of_tendsto hg.continuousAt hF hev, ← hc.self_of_nhds]

/-- `m(z) = 0` away from the zeros. -/
theorem zetaOrder_eq_zero_of_ne {z : ℂ} (hz1 : z ≠ 1) (hζ : riemannZeta z ≠ 0) :
    IEANTN.zetaOrder z = 0 := by
  rw [IEANTN.zetaOrder, meromorphicOrderAt_eq_zero_of_analytic
    (CH2ZetaInstance.analyticAt_riemannZeta hz1) hζ]
  rfl

/-- **The residue sum over `R \ R_C` is minus the weighted zero sum** over the zeros with
`δ < |Im ρ| ≤ T`. An identity of `tsum`s, needing no summability. -/
theorem sumResiduesIn_band_neg (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0) (hx : 0 < x)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T) :
    sumResiduesIn (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s)
        (l.R \ l.RC)
      = -IEANTN.zetaZeroesSum (Set.Iic 1) {t | l.δ < |t| ∧ |t| ≤ l.T}
          (fun ρ ↦ CH2.Phi_lambda lam ε (l.zOf ρ) * (x : ℂ) ^ ρ) := by
  unfold sumResiduesIn IEANTN.zetaZeroesSum
  rw [← tsum_neg, tsum_subtype, tsum_subtype _
    (fun ρ : ℂ ↦ -(CH2.Phi_lambda lam ε (l.zOf ρ) * (x : ℂ) ^ ρ * (IEANTN.zetaOrder ρ : ℂ)))]
  congr 1
  funext z
  have hsub : z ∈ IEANTN.zetaZeroesIn (Set.Iic 1) {t | l.δ < |t| ∧ |t| ≤ l.T} → z ∈ l.R \ l.RC := by
    rintro ⟨hre, ⟨hd, hT⟩, -⟩
    refine ⟨⟨hre, hT⟩, fun hRC ↦ ?_⟩
    exact absurd hRC.2 (not_le.mpr hd)
  by_cases hz : z ∈ l.R \ l.RC
  · rw [Set.indicator_of_mem hz, residue_band_neg l hlam hx hTfree hz]
    by_cases hzz : z ∈ IEANTN.zetaZeroesIn (Set.Iic 1) {t | l.δ < |t| ∧ |t| ≤ l.T}
    · rw [Set.indicator_of_mem hzz]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hzz]
      obtain ⟨⟨hzre, hzT⟩, hzRC⟩ := hz
      have hdlt : l.δ < |z.im| := by
        by_contra hc
        exact hzRC ⟨hzre, not_lt.mp hc⟩
      have hζ : riemannZeta z ≠ 0 := fun h0 ↦ hzz ⟨hzre, ⟨hdlt, hzT⟩, h0⟩
      have hz1 : z ≠ 1 := by
        intro h; rw [h] at hdlt; have := l.hδ.1; simp at hdlt; linarith
      rw [zetaOrder_eq_zero_of_ne hz1 hζ]
      simp
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h ↦ hz (hsub h))]

/-! ### The residues in the band `R_C`: the pole at `σ` and the trivial zeros -/

/-- `coth` at a nonzero real point, bounded through `coth y ≤ 1 + 1/y`. -/
theorem norm_coth_ofReal_le {a : ℝ} (ha : a ≠ 0) : ‖CH2.coth (a : ℂ)‖ ≤ 1 + 1 / |a| := by
  have hc : CH2.coth (a : ℂ) = ((Real.cosh a / Real.sinh a : ℝ) : ℂ) := by
    rw [CH2.coth, ← Complex.ofReal_tanh, Real.tanh_eq_sinh_div_cosh]
    push_cast
    rw [one_div_div]
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (Real.cosh_pos a),
    Real.abs_sinh, ← Real.cosh_abs]
  exact CH2Section7.coth_le_one_add_inv (abs_pos.mpr ha)

/-- `Φ^∘` on the imaginary axis is real `coth`. -/
theorem Phi_circ_I_mul (ν ε u : ℝ) :
    CH2.Phi_circ ν ε (I * (u : ℂ)) = (1 / 2) * (CH2.coth ((Real.pi * u + ν / 2 : ℝ) : ℂ) + ε) := by
  simp only [CH2.Phi_circ]
  congr 2
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The residue of the shifted integrand at the trivial zero `-2(k+1)`, up to sign. -/
noncomputable def trivTerm (l : CH2.LadderParams) (lam ε x : ℝ) (k : ℕ) : ℂ :=
  CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf (-2 * ((k : ℂ) + 1)))
    * (x : ℂ) ^ (-2 * ((k : ℂ) + 1))

/-- **The trivial-zero terms decay geometrically**, with a weight bound `1 + T/(4π)` from
`coth y ≤ 1 + 1/y`: the argument of `coth` is at most `-2π/T` because `σ ≥ 0`. -/
theorem norm_trivTerm_le (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0)
    (hσ0 : 0 ≤ l.sigmaOf lam) (hε : |ε| ≤ 1) (hx : 0 < x) (k : ℕ) :
    ‖trivTerm l lam ε x k‖ ≤ (1 + l.T / (4 * Real.pi)) * (x ^ (-2 : ℝ)) ^ (k + 1) := by
  have hT := l.hT
  have hπ := Real.pi_pos
  have hν : |lam| ≤ 2 * Real.pi / l.T := by
    rw [CH2.LadderParams.sigmaOf] at hσ0
    rw [le_div_iff₀ hT]
    have : l.T * |lam| / (2 * Real.pi) ≤ 1 := by linarith
    rw [div_le_one (by positivity)] at this
    linarith
  set u : ℝ := -(2 * k + 3) / l.T with hu
  have harg : (Real.sign lam : ℂ) * l.zOf (-2 * ((k : ℂ) + 1)) = I * (u : ℂ) := by
    rw [CH2.sign_cast_neg_one hlam, CH2.LadderParams.zOf, hu]
    have hTc : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  set a : ℝ := Real.pi * u + |lam| / 2 with ha
  have ha_le : a ≤ -(2 * Real.pi / l.T) := by
    rw [ha, hu]
    have h1 : Real.pi * (-(2 * (k : ℝ) + 3) / l.T) = -(Real.pi * (2 * k + 3) / l.T) := by ring
    rw [h1]
    have h2 : Real.pi * (2 * (k : ℝ) + 3) / l.T ≥ 3 * Real.pi / l.T := by
      apply div_le_div_of_nonneg_right _ hT.le
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have h3 : |lam| / 2 ≤ Real.pi / l.T := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc |lam| ≤ 2 * Real.pi / l.T := hν
        _ = Real.pi / l.T * 2 := by ring
    have h4 : 3 * Real.pi / l.T = Real.pi / l.T + 2 * Real.pi / l.T := by ring
    linarith
  have hpos : 0 < 2 * Real.pi / l.T := by positivity
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha_le; linarith
  have habs : 1 / |a| ≤ l.T / (2 * Real.pi) := by
    rw [abs_of_neg (by linarith)]
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left (show 2 * Real.pi / l.T ≤ -a by linarith) hT.le
    have h2 : l.T * (2 * Real.pi / l.T) = 2 * Real.pi := by field_simp
    linarith
  have hΦ : ‖CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf (-2 * ((k : ℂ) + 1)))‖
      ≤ 1 + l.T / (4 * Real.pi) := by
    rw [harg, Phi_circ_I_mul, ← ha, norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    have := norm_add_le (CH2.coth (a : ℂ)) (ε : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    have hc := norm_coth_ofReal_le ha0
    have e : l.T / (4 * Real.pi) = (l.T / (2 * Real.pi)) / 2 := by field_simp; ring
    rw [e]
    nlinarith
  have hpow : ‖(x : ℂ) ^ (-2 * ((k : ℂ) + 1))‖ = (x ^ (-2 : ℝ)) ^ (k + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    simp
  rw [trivTerm, norm_mul, hpow]
  exact mul_le_mul_of_nonneg_right hΦ (by positivity)

theorem summable_trivTerm (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0)
    (hσ0 : 0 ≤ l.sigmaOf lam) (hε : |ε| ≤ 1) (hx : 1 < x) :
    Summable (trivTerm l lam ε x) := by
  have hr0 : 0 ≤ x ^ (-2 : ℝ) := by positivity
  have hr1 : x ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  refine Summable.of_norm_bounded ?_ (norm_trivTerm_le l hlam hσ0 hε (by linarith))
  exact ((summable_geometric_of_lt_one hr0 hr1).mul_left (x ^ (-2 : ℝ))).mul_left
    (1 + l.T / (4 * Real.pi)) |>.congr fun k ↦ by ring

/-- **The trivial zeros contribute at most `(1 + T/(4π)) x^{-2}/(1 - x^{-2})`.** -/
theorem norm_tsum_trivTerm_le (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0)
    (hσ0 : 0 ≤ l.sigmaOf lam) (hε : |ε| ≤ 1) (hx : 1 < x) :
    ‖∑' k, trivTerm l lam ε x k‖ ≤ (1 + l.T / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) := by
  have hr0 : 0 ≤ x ^ (-2 : ℝ) := by positivity
  have hr1 : x ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hg := summable_geometric_of_lt_one hr0 hr1
  have hb : Summable (fun k : ℕ ↦ (1 + l.T / (4 * Real.pi)) * (x ^ (-2 : ℝ)) ^ (k + 1)) :=
    (hg.mul_left (x ^ (-2 : ℝ))).mul_left (1 + l.T / (4 * Real.pi)) |>.congr fun k ↦ by ring
  calc ‖∑' k, trivTerm l lam ε x k‖ ≤ ∑' k, ‖trivTerm l lam ε x k‖ :=
        norm_tsum_le_tsum_norm (summable_trivTerm l hlam hσ0 hε hx).norm
    _ ≤ ∑' k : ℕ, (1 + l.T / (4 * Real.pi)) * (x ^ (-2 : ℝ)) ^ (k + 1) :=
        Summable.tsum_le_tsum (fun k ↦ norm_trivTerm_le l hlam hσ0 hε (by linarith) k)
          (summable_trivTerm l hlam hσ0 hε hx).norm hb
    _ = _ := by
        rw [tsum_mul_left]
        congr 1
        simp_rw [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
        field_simp

/-- **The residue of `Φ^∘(-z(s))` at `σ` is `T/(2π)`.** -/
theorem tendsto_sub_mul_Phi_circ_sigma (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam < 0) :
    Tendsto (fun s ↦ (s - ((l.sigmaOf lam : ℝ) : ℂ)) *
        CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s))
      (𝓝[≠] ((l.sigmaOf lam : ℝ) : ℂ)) (𝓝 ((l.T : ℂ) / (2 * Real.pi))) := by
  have hT := l.hT
  have hTc : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  set σc : ℂ := ((l.sigmaOf lam : ℝ) : ℂ) with hσc
  set w₀ : ℂ := ((0 : ℤ) : ℂ) - I * ((|lam| : ℝ) : ℂ) / (2 * Real.pi) with hw₀
  set w : ℂ → ℂ := fun s ↦ (Real.sign lam : ℂ) * l.zOf s with hw
  have hlin : ∀ s, w s - w₀ = (I / l.T) * (s - σc) := by
    intro s
    simp only [hw, hw₀, hσc]
    rw [CH2.sign_cast_neg_one hlam, CH2.LadderParams.zOf, CH2.LadderParams.sigmaOf]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hwc : Continuous w := by
    have : w = fun s ↦ w₀ + (I / l.T) * (s - σc) := by
      funext s; rw [← hlin s]; ring
    rw [this]; fun_prop
  have hwt : Tendsto w (𝓝[≠] σc) (𝓝[≠] w₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := hwc.tendsto σc
      have h0 : w σc = w₀ := by rw [← sub_eq_zero, hlin]; ring
      rw [h0] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h
      have h' : w s - w₀ = 0 := sub_eq_zero.mpr h
      rw [hlin] at h'
      have hI : I / (l.T : ℂ) ≠ 0 := div_ne_zero I_ne_zero hTc
      exact hs (sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hI))
  have hres := (CH2.Phi_circ.residue |lam| ε (abs_pos.mpr hlam.ne) 0).comp hwt
  have hlim := hres.const_mul ((l.T : ℂ) / I)
  have hval : (l.T : ℂ) / I * (I / (2 * Real.pi)) = (l.T : ℂ) / (2 * Real.pi) := by
    field_simp
  rw [hval] at hlim
  refine hlim.congr fun s ↦ ?_
  show (l.T : ℂ) / I * ((w s - w₀) * CH2.Phi_circ |lam| ε (w s)) = _
  rw [hlin]
  field_simp
  rfl

/-- The residue at `σ` of the band integrand: `(T/2π) F(σ) x^σ`. -/
theorem residue_RC_sigma (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0) (hx : 0 < x)
    (hσζ : riemannZeta ((l.sigmaOf lam : ℝ) : ℂ) ≠ 0) :
    residue (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * CH2ZetaInstance.F s *
        (x : ℂ) ^ s) ((l.sigmaOf lam : ℝ) : ℂ)
      = (l.T : ℂ) / (2 * Real.pi) * CH2ZetaInstance.F ((l.sigmaOf lam : ℝ) : ℂ)
          * (x : ℂ) ^ ((l.sigmaOf lam : ℝ) : ℂ) := by
  have hσ1 : ((l.sigmaOf lam : ℝ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [l.sigmaOf_lt_one hlam]
  have hg : ContinuousAt (fun s ↦ CH2ZetaInstance.F s * (x : ℂ) ^ s) ((l.sigmaOf lam : ℝ) : ℂ) :=
    ((CH2ZetaInstance.analyticAt_F_of_zeta_ne_zero hσ1 hσζ).mul
      (CH2ZetaInstance.analyticAt_const_cpow hx _)).continuousAt
  rw [residue_eq_mul_of_tendsto hg (tendsto_sub_mul_Phi_circ_sigma l hlam)
    (Eventually.of_forall fun s ↦ by ring)]
  ring

/-- The residue at a trivial zero of the band integrand: `-trivTerm k`. -/
theorem residue_RC_trivial (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0) (hx : 0 < x)
    (hσ0 : 0 ≤ l.sigmaOf lam) (k : ℕ) :
    residue (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * CH2ZetaInstance.F s *
        (x : ℂ) ^ s) (-2 * ((k : ℂ) + 1)) = -trivTerm l lam ε x k := by
  have hre : (-2 * ((k : ℂ) + 1)).re = -2 * ((k : ℝ) + 1) := by simp
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (-2 * ((k : ℂ) + 1)) ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hav : l.AvoidsWeightPoles lam (-2 * ((k : ℂ) + 1)) :=
    l.avoidsWeightPoles_of_re_ne (by rw [hre]; linarith)
  have hg : ContinuousAt (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
      (x : ℂ) ^ s) (-2 * ((k : ℂ) + 1)) :=
    ((l.analyticAt_Phi_circ_neg hlam hav).mul
      (CH2ZetaInstance.analyticAt_const_cpow hx _)).continuousAt
  rw [residue_eq_mul_of_tendsto hg (tendsto_sub_mul_F h1)
    (Eventually.of_forall fun s ↦ by ring), zetaOrder_trivial, trivTerm]
  simp

/-- **The partial residue sums over `R_C`**: the pole at `σ` and the trivial zeros to the right of
`σ_n = 1 - 2n`, given that the zeros of `ζ` in `R_C` are all in `Re < 0`. -/
theorem sumResiduesIn_RC_partial (l : CH2.LadderParams) {lam ε x : ℝ}
    (hsig : l.σ = CH2ZetaInstance.sigmaZeta) (hlam : lam < 0) (hx : 0 < x)
    (hσ0 : 0 ≤ l.sigmaOf lam) (hσζ : riemannZeta ((l.sigmaOf lam : ℝ) : ℂ) ≠ 0)
    (hRC : ∀ z ∈ l.RC, riemannZeta z = 0 → z.re < 0) {n : ℕ} (hn : 1 ≤ n) :
    sumResiduesIn (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
        CH2ZetaInstance.F s * (x : ℂ) ^ s) (l.RC ∩ {z | l.σ n < z.re})
      = (l.T : ℂ) / (2 * Real.pi) * CH2ZetaInstance.F ((l.sigmaOf lam : ℝ) : ℂ)
          * (x : ℂ) ^ ((l.sigmaOf lam : ℝ) : ℂ)
        - ∑ k ∈ Finset.range (n - 1), trivTerm l lam ε x k := by
  set g : ℂ → ℂ := fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
    CH2ZetaInstance.F s * (x : ℂ) ^ s with hg_def
  set S : Set ℂ := l.RC ∩ {z | l.σ n < z.re} with hS
  set σc : ℂ := ((l.sigmaOf lam : ℝ) : ℂ) with hσc
  set A : Finset ℂ := insert σc ((Finset.range (n - 1)).image (fun k : ℕ ↦ -2 * ((k : ℂ) + 1)))
    with hA_def
  have hσn : l.σ n = 1 - 2 * n := by rw [hsig]; rfl
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd := l.hδ
  have hT := l.hT
  have hσ1 := l.sigmaOf_lt_one hlam
  have hmem_triv : ∀ k : ℕ, -2 * ((k : ℂ) + 1) ∈ S ↔ k < n - 1 := by
    intro k
    simp only [hS, CH2.LadderParams.RC, Set.mem_inter_iff, Set.mem_ofPred_eq, hσn]
    have hre : (-2 * ((k : ℂ) + 1)).re = -2 * ((k : ℝ) + 1) := by simp
    have him : (-2 * ((k : ℂ) + 1)).im = 0 := by simp
    rw [hre, him, abs_zero]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    constructor
    · rintro ⟨-, h⟩
      have : (2 * k + 3 : ℝ) < 2 * n := by linarith
      have : 2 * k + 3 < 2 * n := by exact_mod_cast this
      omega
    · intro h
      have : 2 * k + 3 < 2 * n := by omega
      have : (2 * k + 3 : ℝ) < 2 * n := by exact_mod_cast this
      exact ⟨⟨by linarith, hd.1.le⟩, by linarith⟩
  have hσS : σc ∈ S := by
    simp only [hS, hσc, CH2.LadderParams.RC, Set.mem_inter_iff, Set.mem_ofPred_eq, hσn,
      Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨⟨hσ1.le, hd.1.le⟩, by linarith⟩
  have hAS : ∀ z ∈ A, z ∈ S := by
    intro z hz
    rw [hA_def, Finset.mem_insert, Finset.mem_image] at hz
    rcases hz with rfl | ⟨k, hk, rfl⟩
    · exact hσS
    · exact (hmem_triv k).mpr (Finset.mem_range.mp hk)
  have hres0 : ∀ z ∈ S, z ∉ A → residue g z = 0 := by
    intro z hzS hzA
    rw [hA_def, Finset.mem_insert, Finset.mem_image, not_or] at hzA
    obtain ⟨hzσ, hztriv⟩ := hzA
    have hnottriv : ∀ m : ℕ, z ≠ -2 * ((m : ℂ) + 1) := by
      intro m hm
      exact hztriv ⟨m, Finset.mem_range.mpr ((hmem_triv m).mp (hm ▸ hzS)), hm.symm⟩
    have hav : l.AvoidsWeightPoles lam z := by
      by_contra hc
      have hzim : |z.im| ≤ l.δ := hzS.1.2
      have hdT : l.δ < l.T / 4 := hd.2
      rcases CH2ZetaInstance.weight_pole_cases l (by linarith) hc with h | h
      · exact hzσ h
      · linarith
    have hF : AnalyticAt ℂ CH2ZetaInstance.F z := by
      by_cases h1 : z = 1
      · rw [h1]; exact CH2ZetaInstance.analyticAt_F_one
      · refine CH2ZetaInstance.analyticAt_F_of_zeta_ne_zero h1 fun h0 ↦ ?_
        exact CH2ZetaInstance.riemannZeta_ne_zero_of_re_neg (hRC z hzS.1 h0) hnottriv h0
    exact residue_analyticAt_eq_zero
      (((l.analyticAt_Phi_circ_neg hlam hav).mul hF).mul
        (CH2ZetaInstance.analyticAt_const_cpow hx z))
  have hσA : σc ∉ (Finset.range (n - 1)).image (fun k : ℕ ↦ -2 * ((k : ℂ) + 1)) := by
    rw [Finset.mem_image]
    rintro ⟨k, -, hk⟩
    have := congrArg Complex.re hk
    simp only [hσc, Complex.ofReal_re] at this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (-2 * ((k : ℂ) + 1)).re = -2 * ((k : ℝ) + 1) := by simp
    linarith
  have hinj : Set.InjOn (fun k : ℕ ↦ -2 * ((k : ℂ) + 1)) (Finset.range (n - 1) : Set ℕ) := by
    intro a _ b _ hab
    have := congrArg Complex.re hab
    simp only at this
    have e : ∀ m : ℕ, (-2 * ((m : ℂ) + 1)).re = -2 * ((m : ℝ) + 1) := fun m ↦ by simp
    rw [e, e] at this
    exact_mod_cast (by linarith : (a : ℝ) = b)
  unfold sumResiduesIn
  rw [tsum_subtype, tsum_eq_sum (s := A)]
  · rw [Finset.sum_congr rfl (fun z hz ↦ Set.indicator_of_mem (hAS z hz) _),
      hA_def, Finset.sum_insert hσA, Finset.sum_image hinj, residue_RC_sigma l hlam hx hσζ,
      Finset.sum_congr rfl (fun k _ ↦ residue_RC_trivial l hlam hx hσ0 k),
      Finset.sum_neg_distrib, sub_eq_add_neg]
  · intro z hz
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS]; exact hres0 z hzS hz
    · exact Set.indicator_of_notMem hzS _

/-- **The `R_C` residue limit**: `(T/2π) F(σ) x^σ` minus the whole trivial-zero series. -/
theorem sumResiduesLim_RC (l : CH2.LadderParams) {lam ε x : ℝ}
    (hsig : l.σ = CH2ZetaInstance.sigmaZeta) (hlam : lam < 0) (hx : 1 < x) (hε : |ε| ≤ 1)
    (hσ0 : 0 ≤ l.sigmaOf lam) (hσζ : riemannZeta ((l.sigmaOf lam : ℝ) : ℂ) ≠ 0)
    (hRC : ∀ z ∈ l.RC, riemannZeta z = 0 → z.re < 0) :
    l.sumResiduesLim (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
        CH2ZetaInstance.F s * (x : ℂ) ^ s) l.RC
      = (l.T : ℂ) / (2 * Real.pi) * CH2ZetaInstance.F ((l.sigmaOf lam : ℝ) : ℂ)
          * (x : ℂ) ^ ((l.sigmaOf lam : ℝ) : ℂ)
        - ∑' k, trivTerm l lam ε x k := by
  unfold CH2.LadderParams.sumResiduesLim
  apply Tendsto.limUnder_eq
  have h1 := ((summable_trivTerm l hlam hσ0 hε hx).hasSum.tendsto_sum_nat).comp
    (tendsto_sub_atTop_nat 1)
  refine (tendsto_const_nhds.sub h1).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sumResiduesIn_RC_partial l hsig hlam (by linarith) hσ0 hσζ hRC hn]
  rfl

end CH2Section6
