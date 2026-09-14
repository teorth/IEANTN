/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section6Res

/-!
# Section 6: the weight at the zeros

`svm_bounds_explicit` leaves the zero sum `∑ m(ρ) Φ_λ(z(ρ)) x^ρ`. This file puts the weight in the
paper's form (`lem:omlet`, eq. `explorm`): for `Im s > 0` and `λ = 2π(σ-1)/T < 0`,

  `Φ_λ(z(s)) = -(i/2) (ω⁺_{T,σ}(s) + ε i θ_{T,1}(s))`,

with `θ_{T,σ}(s) = 1 - (s-σ)/(iT)`, `c_{T,σ} = θ_{T,σ}(1+iT) cot(π θ_{T,σ}(1+iT))` and
`ω⁺_{T,σ}(s) = -θ_{T,σ}(s) cot(π θ_{T,σ}(s)) + c_{T,σ}`. So `|Φ_λ(z(ρ))|` is half the quantity
`prop:vihuela` bounds, with `ξ = ε`.
-/

open Complex Filter Topology

namespace CH2Section6

/-- `θ_{T,σ}(s) = 1 - (s-σ)/(iT)`. -/
noncomputable def thetaTS (T σ : ℝ) (s : ℂ) : ℂ := 1 - (s - σ) / (I * T)

/-- `c_{T,σ} = θ_{T,σ}(1+iT) cot(π θ_{T,σ}(1+iT))`. -/
noncomputable def cTS (T σ : ℝ) : ℂ :=
  thetaTS T σ (1 + I * T) * Complex.cot (Real.pi * thetaTS T σ (1 + I * T))

/-- `ω⁺_{T,σ}(s) = -θ_{T,σ}(s) cot(π θ_{T,σ}(s)) + c_{T,σ}`. -/
noncomputable def omegaPlus (T σ : ℝ) (s : ℂ) : ℂ :=
  -(thetaTS T σ s * Complex.cot (Real.pi * thetaTS T σ s)) + cTS T σ

theorem coth_eq_cosh_div_sinh (y : ℂ) : CH2.coth y = Complex.cosh y / Complex.sinh y := by
  rw [CH2.coth, Complex.tanh_eq_sinh_div_cosh, one_div_div]

theorem cot_pi_add (x : ℂ) : Complex.cot ((Real.pi : ℂ) + x) = Complex.cot x := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, add_comm, Complex.sin_add_pi,
    Complex.cos_add_pi, neg_div_neg_eq]

theorem cot_I_mul (y : ℂ) :
    Complex.cot (I * y) = -I * (Complex.cosh y / Complex.sinh y) := by
  rw [Complex.cot_eq_cos_div_sin, mul_comm I y, Complex.cos_mul_I, Complex.sin_mul_I]
  rcases eq_or_ne (Complex.sinh y) 0 with h | h
  · simp [h]
  · field_simp
    rw [I_sq]
    ring

/-- **`lem:omlet`, eq. `explorm`, for `λ < 0`.** No pole condition is needed: at a pole of `coth`
both sides take Lean's junk value consistently. -/
theorem Phi_lambda_omlet (l : CH2.LadderParams) {σ ε : ℝ} (hσ1 : σ < 1) {s : ℂ}
    (hs : 0 < s.im) :
    CH2.Phi_lambda (lamOf l.T σ) ε (l.zOf s)
      = -(I / 2) * (omegaPlus l.T σ s + ε * I * thetaTS l.T 1 s) := by
  have hT := l.hT
  have hTc : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hπ := Real.pi_pos
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
  have hlam : lamOf l.T σ < 0 := lamOf_neg hT hσ1
  have hν : |lamOf l.T σ| = 2 * Real.pi * (1 - σ) / l.T := by
    rw [abs_of_neg hlam, lamOf]; ring
  have hre : 0 < (l.zOf s).re := by
    rw [CH2ZetaInstance.re_zOf]; exact div_pos hs hT
  set W : ℂ := 2 * Real.pi * (s - σ) / l.T with hW
  set ν : ℝ := 2 * Real.pi * (1 - σ) / l.T with hν_def
  have hνpos : 0 < ν := by
    rw [hν_def]; apply div_pos _ hT; nlinarith
  have hW0 : W ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [hW] at this
    simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im,
      Complex.zero_im] at this
    simp at this
    rcases this with h1 | h1
    · linarith
    · linarith
  have hz : l.zOf s = (s - 1) / (I * l.T) := rfl
  have harg : -2 * (Real.pi : ℂ) * I * ((((Real.sign (lamOf l.T σ)) : ℝ) : ℂ) * l.zOf s)
      + ((|lamOf l.T σ| : ℝ) : ℂ) = W := by
    rw [CH2.sign_cast_neg_one hlam, hν, hz, hW, hν_def]
    push_cast
    field_simp
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four]
    try ring
  have hB : CH2.B ε W = W * (CH2.coth (W / 2) + ε) / 2 := by rw [CH2.B, if_neg hW0]
  have hBν : CH2.B ε ((|lamOf l.T σ| : ℝ) : ℂ) = (ν : ℂ) * (CH2.coth ((ν : ℂ) / 2) + ε) / 2 := by
    rw [hν, CH2.B, if_neg (Complex.ofReal_ne_zero.mpr hνpos.ne')]
  -- the paper's quantities in terms of `coth`
  have hθ : (Real.pi : ℂ) * thetaTS l.T σ s = (Real.pi : ℂ) + I * (W / 2) := by
    rw [thetaTS, hW]
    field_simp
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four]
    try ring
  have hθ1 : (Real.pi : ℂ) * thetaTS l.T σ (1 + I * l.T) = I * ((ν : ℂ) / 2) := by
    rw [thetaTS, hν_def]
    push_cast
    field_simp
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four]
    try ring
  have hθs : thetaTS l.T σ s = 1 + I * W / (2 * Real.pi) := by
    rw [thetaTS, hW]
    field_simp
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four]
    try ring
  have hθs1 : thetaTS l.T σ (1 + I * l.T) = I * (ν : ℂ) / (2 * Real.pi) := by
    rw [thetaTS, hν_def]
    push_cast
    field_simp
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four]
    try ring
  have hθ1s : thetaTS l.T 1 s = 1 - l.zOf s := by
    simp [thetaTS, hz]
  have hzW : l.zOf s = (W - ν) / (2 * Real.pi * I) := by
    rw [hz, hW, hν_def]
    push_cast
    field_simp
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four]
    try ring
  simp only [CH2.Phi_lambda, CH2.Phi_circ, CH2.Phi_star]
  rw [Real.sign_of_pos hre, harg, hB, hBν, omegaPlus, cTS, hθ, hθ1, cot_pi_add, cot_I_mul,
    cot_I_mul, hθs, hθs1, hθ1s, hzW, coth_eq_cosh_div_sinh, coth_eq_cosh_div_sinh,
    CH2.sign_cast_neg_one hlam]
  push_cast
  field_simp
  ring_nf
  try simp only [I_sq, I_pow_three, I_pow_four]
  try ring

/-- `|Φ_λ(z(s))| = |ω⁺_{T,σ}(s) + ε i θ_{T,1}(s)|/2` above the axis. -/
theorem norm_Phi_lambda_omlet (l : CH2.LadderParams) {σ ε : ℝ} (hσ1 : σ < 1) {s : ℂ}
    (hs : 0 < s.im) :
    ‖CH2.Phi_lambda (lamOf l.T σ) ε (l.zOf s)‖
      = ‖omegaPlus l.T σ s + ε * I * thetaTS l.T 1 s‖ / 2 := by
  rw [Phi_lambda_omlet l hσ1 hs, norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_ofNat]
  ring

/-! ### Conjugation symmetry and the zero sum -/

/-- **eq. `Phicong`**: `Φ_λ(z(s̄)) = \overline{Φ_λ(z(s))}`. -/
theorem Phi_lambda_zOf_conj (l : CH2.LadderParams) (lam ε : ℝ) (s : ℂ) :
    CH2.Phi_lambda lam ε (l.zOf (starRingEnd ℂ s))
      = starRingEnd ℂ (CH2.Phi_lambda lam ε (l.zOf s)) := by
  have hc : ∀ u : ℂ, CH2.Phi_circ |lam| ε (-(starRingEnd ℂ u))
      = starRingEnd ℂ (CH2.Phi_circ |lam| ε u) := by
    intro u
    simp only [CH2.Phi_circ, map_mul, map_add, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
      CH2.coth_conj]
    congr 3
    simp only [map_add, map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hsgn : ((Real.sign lam : ℝ) : ℂ) * -(starRingEnd ℂ (l.zOf s))
      = -(starRingEnd ℂ (((Real.sign lam : ℝ) : ℂ) * l.zOf s)) := by
    simp only [map_mul, Complex.conj_ofReal]; ring
  have hre : (l.zOf (starRingEnd ℂ s)).re = -(l.zOf s).re := by
    rw [l.zOf_conj]; simp
  simp only [CH2.Phi_lambda]
  rw [l.zOf_conj, hsgn, hc, CH2.Phi_star_conj_neg]
  rw [show (-(starRingEnd ℂ (l.zOf s))).re = -(l.zOf s).re by simp, Real.sign_neg]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- `m(ρ̄) = m(ρ)`. -/
theorem zetaOrder_conj (ρ : ℂ) : IEANTN.zetaOrder (starRingEnd ℂ ρ) = IEANTN.zetaOrder ρ := by
  have h := CH2.meromorphicOrderAt_conj_reflect (G := riemannZeta) (a := ρ)
  have e : (fun w ↦ starRingEnd ℂ (riemannZeta (starRingEnd ℂ w))) = riemannZeta := by
    funext w
    rw [riemannZeta_conj, Complex.conj_conj]
  change meromorphicOrderAt (fun w ↦ starRingEnd ℂ (riemannZeta (starRingEnd ℂ w)))
    (starRingEnd ℂ ρ) = _ at h
  rw [e] at h
  rw [IEANTN.zetaOrder, IEANTN.zetaOrder, h]

/-- The zeros with `δ < |Im| ≤ T` left of `Re s = 1` are finitely many. -/
theorem finite_zeros_band (l : CH2.LadderParams) :
    (IEANTN.zetaZeroesIn (Set.Iic 1) {t | l.δ < |t| ∧ |t| ≤ l.T}).Finite := by
  have hd := l.hδ.1
  set K : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ l.δ ≤ |z.im| ∧ |z.im| ≤ l.T} with hK
  have hKc : IsCompact K := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    refine ⟨?_, ?_⟩
    · refine (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_im.abs).inter
            (isClosed_le Complex.continuous_im.abs continuous_const)))
    · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1 + l.T, fun z hz ↦ ?_⟩
      obtain ⟨h0, h1, -, h3⟩ := hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 + l.T := by rw [abs_of_nonneg h0]; linarith
  have h1K : (1 : ℂ) ∉ K := by
    intro h; have := h.2.2.1; simp at this; linarith
  refine (CH2ZetaInstance.finite_zeros_riemannZeta_of_isCompact hKc h1K).subset ?_
  rintro z ⟨hre, ⟨hdz, hTz⟩, hz⟩
  have him : z.im ≠ 0 := by intro h; rw [h, abs_zero] at hdz; linarith
  have hs := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hz him
  exact ⟨⟨hs.1, hs.2, hdz.le, hTz⟩, hz⟩

/-- At a zero, `m(ρ) ≥ 0`. -/
theorem zetaOrder_nonneg_of_ne_one {ρ : ℂ} (hρ : ρ ≠ 1) : 0 ≤ IEANTN.zetaOrder ρ := by
  have ha := CH2ZetaInstance.analyticAt_riemannZeta hρ
  rw [IEANTN.zetaOrder, ha.meromorphicOrderAt_eq]
  rcases analyticOrderAt riemannZeta ρ with _ | n
  · exact le_refl 0
  · exact Int.natCast_nonneg n

/-- **The zero sum, bounded by the `ω⁺` sum above the axis.** Each conjugate pair contributes
`2 · |ω⁺(ρ) + ε i θ_{T,1}(ρ)|/2 · x^{Re ρ} m(ρ)`. -/
theorem abs_re_zeroTerm_le (l : CH2.LadderParams) {σ ε x : ℝ} (hσ1 : σ < 1) (hx : 0 < x) :
    |(zeroTerm l (lamOf l.T σ) ε x).re|
      ≤ IEANTN.zetaZeroesSum (Set.Iic 1) (Set.Ioc l.δ l.T)
          (fun ρ ↦ ‖omegaPlus l.T σ ρ + ε * I * thetaTS l.T 1 ρ‖ * x ^ ρ.re) := by
  have hd := l.hδ.1
  set A := IEANTN.zetaZeroesIn (Set.Iic 1) {t | l.δ < |t| ∧ |t| ≤ l.T} with hA
  set Ap := IEANTN.zetaZeroesIn (Set.Iic 1) (Set.Ioc l.δ l.T) with hAp
  set Am := IEANTN.zetaZeroesIn (Set.Iic 1) (Set.Ico (-l.T) (-l.δ)) with hAm
  have hfin : A.Finite := finite_zeros_band l
  have hApA : Ap ⊆ A := by
    rintro z ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨h1, ⟨by rw [abs_of_pos (by linarith)]; exact h2,
      by rw [abs_of_pos (by linarith)]; exact h3⟩, h4⟩
  have hAmA : Am ⊆ A := by
    rintro z ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨h1, ⟨by rw [abs_of_neg (by linarith)]; linarith,
      by rw [abs_of_neg (by linarith)]; linarith⟩, h4⟩
  have hunion : A = Ap ∪ Am := by
    ext z
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
      rcases le_or_gt 0 z.im with h | h
      · left; rw [abs_of_nonneg h] at h2 h3; exact ⟨h1, ⟨h2, h3⟩, h4⟩
      · right; rw [abs_of_neg h] at h2 h3; exact ⟨h1, ⟨by linarith, by linarith⟩, h4⟩
    · rintro (h | h)
      · exact hApA h
      · exact hAmA h
  have hdisj : Disjoint Ap Am := by
    rw [Set.disjoint_left]
    rintro z ⟨-, ⟨h2, -⟩, -⟩ ⟨-, ⟨-, h3⟩, -⟩
    linarith
  set g : ℂ → ℝ := fun ρ ↦ ‖CH2.Phi_lambda (lamOf l.T σ) ε (l.zOf ρ)‖ * x ^ ρ.re
    * (IEANTN.zetaOrder ρ : ℝ) with hg
  haveI : Finite A := hfin.to_subtype
  haveI : Finite Ap := (hfin.subset hApA).to_subtype
  haveI : Finite Am := (hfin.subset hAmA).to_subtype
  have hne1 : ∀ ρ ∈ A, ρ ≠ 1 := by
    rintro ρ ⟨-, ⟨h2, -⟩, -⟩ rfl
    simp at h2; linarith
  -- the norm bound, term by term
  have hterm : ∀ ρ : A, ‖CH2.Phi_lambda (lamOf l.T σ) ε (l.zOf ρ) * (x : ℂ) ^ (ρ : ℂ)
      * ((IEANTN.zetaOrder ρ : ℤ) : ℂ)‖ = g ρ := by
    intro ρ
    have hm := zetaOrder_nonneg_of_ne_one (hne1 ρ ρ.2)
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hg]
    congr 1
    rw [Complex.norm_intCast]
    exact_mod_cast abs_of_nonneg hm
  have h1 : |(zeroTerm l (lamOf l.T σ) ε x).re| ≤ ∑' ρ : A, g ρ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [zeroTerm, IEANTN.zetaZeroesSum]
    refine (norm_tsum_le_tsum_norm (Summable.of_finite)).trans (le_of_eq ?_)
    exact tsum_congr hterm
  -- split into the two half-planes and fold the lower one onto the upper one
  have h2 : ∑' ρ : A, g ρ = ∑' ρ : Ap, g ρ + ∑' ρ : Am, g ρ := by
    rw [show (∑' ρ : A, g ρ) = ∑' ρ : ↑(Ap ∪ Am), g ρ by rw [← hunion]]
    exact Summable.tsum_union_disjoint hdisj Summable.of_finite Summable.of_finite
  have hconjmem : ∀ ρ ∈ Ap, starRingEnd ℂ ρ ∈ Am := by
    rintro ρ ⟨h1, ⟨h2, h3⟩, h4⟩
    refine ⟨by simpa using h1, ⟨by simp; linarith, by simp; linarith⟩, ?_⟩
    show riemannZeta _ = 0
    rw [riemannZeta_conj, show riemannZeta ρ = 0 from h4, map_zero]
  have hconjmem' : ∀ ρ ∈ Am, starRingEnd ℂ ρ ∈ Ap := by
    rintro ρ ⟨h1, ⟨h2, h3⟩, h4⟩
    refine ⟨by simpa using h1, ⟨by simp; linarith, by simp; linarith⟩, ?_⟩
    show riemannZeta _ = 0
    rw [riemannZeta_conj, show riemannZeta ρ = 0 from h4, map_zero]
  let e : Ap ≃ Am :=
    { toFun := fun ρ ↦ ⟨starRingEnd ℂ ρ, hconjmem ρ ρ.2⟩
      invFun := fun ρ ↦ ⟨starRingEnd ℂ ρ, hconjmem' ρ ρ.2⟩
      left_inv := fun ρ ↦ by ext; simp
      right_inv := fun ρ ↦ by ext; simp }
  have h3 : ∑' ρ : Am, g ρ = ∑' ρ : Ap, g ρ := by
    rw [← e.tsum_eq]
    refine tsum_congr fun ρ ↦ ?_
    show g (starRingEnd ℂ ρ) = g ρ
    rw [hg]
    simp only
    rw [Phi_lambda_zOf_conj, zetaOrder_conj, Complex.conj_re, norm_conj]
  have h4 : ∀ ρ : Ap, g ρ = (‖omegaPlus l.T σ ρ + ε * I * thetaTS l.T 1 ρ‖ * x ^ (ρ : ℂ).re
      * (IEANTN.zetaOrder ρ : ℝ)) / 2 := by
    intro ρ
    have him : 0 < (ρ : ℂ).im := lt_trans hd ρ.2.2.1.1
    rw [hg]
    simp only
    rw [norm_Phi_lambda_omlet l hσ1 him]
    ring
  calc |(zeroTerm l (lamOf l.T σ) ε x).re| ≤ ∑' ρ : A, g ρ := h1
    _ = 2 * ∑' ρ : Ap, g ρ := by rw [h2, h3]; ring
    _ = _ := by
      rw [IEANTN.zetaZeroesSum, tsum_congr h4, tsum_div_const]
      ring

/-! ### The two-sided bound -/

/-- `Re φ_±(0) = ½ coth(π(1-σ)/T) ± ½`. -/
theorem re_phiNeg_zero (T σ ε : ℝ) (hT : 0 < T) (hσ1 : σ < 1) :
    (phiNeg |lamOf T σ| ε 0).re
      = (1 / 2) * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T)) + ε / 2 := by
  have hν : |lamOf T σ| / 2 = Real.pi * (1 - σ) / T := by
    rw [abs_of_neg (lamOf_neg hT hσ1), lamOf]; ring
  rw [phiNeg_zero]
  have hc : CH2.coth (((|lamOf T σ| : ℝ) : ℂ) / 2)
      = ((Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T) : ℝ) : ℂ) := by
    rw [coth_eq_cosh_div_sinh, show (((|lamOf T σ| : ℝ) : ℂ) / 2) = ((|lamOf T σ| / 2 : ℝ) : ℂ) by
      push_cast; ring, hν, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast; rfl
  rw [hc]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

/-- **`|ψ_σ(x)/x^{1-σ} - Main| ≤ π/T + (2π/(Tx))(Z + Tr + E)`** for `σ ∈ [0, 1)`, where `Main` is
`(π/T) coth(π(1-σ)/T) - (ζ'/ζ)(σ) x^{σ-1}` and `Z`, `E` are any bounds on the `ω⁺` zero sums and
the shift errors for both signs. -/
theorem svm_abs_bound
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    {l : CH2.LadderParams} (hsig : l.σ = CH2ZetaInstance.sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hRC : ∀ z ∈ l.RC, riemannZeta z = 0 → z.re < 0)
    {σ x₀ x : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0)
    (hx₀ : 1 < x₀) (hx : x₀ < x) {Z E : ℝ}
    (hZ : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      IEANTN.zetaZeroesSum (Set.Iic 1) (Set.Ioc l.δ l.T)
          (fun ρ ↦ ‖omegaPlus l.T σ ρ + ε * I * thetaTS l.T 1 ρ‖ * x ^ ρ.re) ≤ Z)
    (hE : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → shiftError l (lamOf l.T σ) ε x ≤ E) :
    |Svm σ x / x ^ (1 - σ)
        - (Real.pi / l.T * (Real.cosh (Real.pi * (1 - σ) / l.T) / Real.sinh (Real.pi * (1 - σ) / l.T))
          - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
      ≤ Real.pi / l.T + 2 * Real.pi / (l.T * x) *
          (Z + (1 + l.T / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) + E) := by
  have hT := l.hT
  have hπ := Real.pi_pos
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlam : lamOf l.T σ < 0 := lamOf_neg hT hσ1
  have hσ' : l.sigmaOf (lamOf l.T σ) = σ := sigmaOf_lamOf l hσ1
  obtain ⟨hup, hlo⟩ := svm_bounds_explicit hfe hdig hsig hTfree hRC hσ0 hσ1 hσζ hx₀ hx
  set C := Real.cosh (Real.pi * (1 - σ) / l.T) / Real.sinh (Real.pi * (1 - σ) / l.T) with hC
  set D := (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re with hD
  set B := (1 + l.T / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) with hB
  set p := x ^ (1 - σ) with hp
  have hppos : 0 < p := Real.rpow_pos_of_pos hxpos _
  have hZε : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → |(zeroTerm l (lamOf l.T σ) ε x).re| ≤ Z :=
    fun ε hε ↦ (abs_re_zeroTerm_le l hσ1 hxpos).trans (hZ ε hε)
  have hTr : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → |(∑' k, trivTerm l (lamOf l.T σ) ε x k).re| ≤ B := by
    intro ε hε
    have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    exact (Complex.abs_re_le_norm _).trans
      (norm_tsum_trivTerm_le l hlam (by rw [hσ']; exact hσ0) hε1 hx1)
  -- `x^{-σ} = p/x` and `x^{σ-1} = 1/p`
  have hxs : x ^ (-σ) = p / x := by
    rw [hp, show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hxpos, Real.rpow_one]
    field_simp
  have hxs1 : x ^ (σ - 1) = 1 / p := by
    rw [hp, show σ - 1 = -(1 - σ) by ring, Real.rpow_neg hxpos.le, one_div]
  rw [re_phiNeg_zero l.T σ 1 hT hσ1, ← hC] at hup
  rw [re_phiNeg_zero l.T σ (-1) hT hσ1, ← hC] at hlo
  rw [hxs] at hup hlo
  rw [hxs1, abs_le]
  have hK : 0 ≤ 2 * Real.pi * (p / x) / l.T := by positivity
  constructor
  · -- lower bound
    have hZ1 := abs_le.mp (hZε (-1) (Or.inr rfl))
    have hT1 := abs_le.mp (hTr (-1) (Or.inr rfl))
    have hE1 := hE (-1) (Or.inr rfl)
    have hin : -(Z + B + E) ≤ -(zeroTerm l (lamOf l.T σ) (-1) x).re
        - (∑' k, trivTerm l (lamOf l.T σ) (-1) x k).re - shiftError l (lamOf l.T σ) (-1) x := by
      linarith [hZ1.2, hT1.2]
    have h := mul_le_mul_of_nonneg_left hin hK
    have hS : p * (Real.pi / l.T * C - D * (1 / p) - (Real.pi / l.T
        + 2 * Real.pi / (l.T * x) * (Z + B + E))) ≤ Svm σ x := by
      have e1 : p * (Real.pi / l.T * C - D * (1 / p) - (Real.pi / l.T
          + 2 * Real.pi / (l.T * x) * (Z + B + E)))
          = 2 * Real.pi * p / l.T * ((1 / 2) * C + -1 / 2) - D
            + 2 * Real.pi * (p / x) / l.T * (-(Z + B + E)) := by
        field_simp
        ring
      rw [e1]
      linarith
    have key : Real.pi / l.T * C - D * (1 / p) - (Real.pi / l.T
        + 2 * Real.pi / (l.T * x) * (Z + B + E)) ≤ Svm σ x / p := by
      rw [le_div_iff₀ hppos, mul_comm]; exact hS
    linarith
  · -- upper bound
    have hZ1 := abs_le.mp (hZε 1 (Or.inl rfl))
    have hT1 := abs_le.mp (hTr 1 (Or.inl rfl))
    have hE1 := hE 1 (Or.inl rfl)
    have hin : -(zeroTerm l (lamOf l.T σ) 1 x).re
        - (∑' k, trivTerm l (lamOf l.T σ) 1 x k).re + shiftError l (lamOf l.T σ) 1 x ≤ Z + B + E := by
      linarith [hZ1.1, hT1.1]
    have h := mul_le_mul_of_nonneg_left hin hK
    have hS : Svm σ x ≤ p * (Real.pi / l.T * C - D * (1 / p) + (Real.pi / l.T
        + 2 * Real.pi / (l.T * x) * (Z + B + E))) := by
      have e1 : p * (Real.pi / l.T * C - D * (1 / p) + (Real.pi / l.T
          + 2 * Real.pi / (l.T * x) * (Z + B + E)))
          = 2 * Real.pi * p / l.T * ((1 / 2) * C + 1 / 2) - D
            + 2 * Real.pi * (p / x) / l.T * (Z + B + E) := by
        field_simp
        ring
      rw [e1]
      linarith
    have key : Svm σ x / p ≤ Real.pi / l.T * C - D * (1 / p) + (Real.pi / l.T
        + 2 * Real.pi / (l.T * x) * (Z + B + E)) := by
      rw [div_le_iff₀ hppos, mul_comm]; exact hS
    linarith

end CH2Section6
