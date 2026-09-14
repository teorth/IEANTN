/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section6
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

end CH2Section6
