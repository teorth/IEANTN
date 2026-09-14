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

end CH2Section6
