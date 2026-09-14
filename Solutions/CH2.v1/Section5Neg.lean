/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section5

/-!
# Proposition 5.2 for `λ < 0`

The port of §5 proves `prop_5_2` only for `λ > 0`, and `λ = 2π(σ-1)/T`, so it covers `σ > 1`. Every
consumer on the path to Corollary 1.2 needs `σ < 1`: `σ = 0` for `ψ`, and `σ → 1⁻` for `∑ Λ(n)/n`.
This file supplies the missing sign.

## What changes

For `λ > 0` the weights are evaluated at `z(s) = (s-1)/(iT)`, which lies in the closed upper
half-plane for every `s ∈ R`, and `Φ^∘`, `Φ^⋆` are uniformly controlled there; their poles pull
back to `Re s > 1`, off `R` altogether.

For `λ < 0` they are evaluated at `-z(s)`, and the poles pull back to

  `s = σ + ikT`,   `σ = 1 - T|λ|/(2π) < 1`,

inside `R`: at `s = σ` (a pole of `Φ^∘`, whose residue is the whole point of the `λ < 0` case), and at
`σ ± iT` on the horizontal edges (poles of both `Φ^∘` and `Φ^⋆`, which cancel in `Φ_λ`).

## How the bounds are recovered

Left of `Re s = σ - m` the weights are controlled by `ϕ_circ_bound_left` and `ϕ_star_bound_left`,
already in `Approximants`. The ladder columns all lie there. What is left of the contour is compact
and misses every pole, because the contour runs at height `δ ∈ (0, T/4)`, so continuity bounds it.
-/

open Real Complex

namespace CH2

/-- The abscissa `σ = 1 - T|λ|/(2π)` of the weights' poles when `λ < 0`. -/
noncomputable def LadderParams.sigmaOf (l : LadderParams) (lam : ℝ) : ℝ :=
  1 - l.T * |lam| / (2 * π)

/-- The points `σ + ikT` where the `λ < 0` weights may have poles. -/
def LadderParams.AvoidsWeightPoles (l : LadderParams) (lam : ℝ) (s : ℂ) : Prop :=
  ∀ k : ℤ, s ≠ ((l.sigmaOf lam : ℝ) : ℂ) + (k : ℂ) * (l.T : ℂ) * I

/-- `-z(s)` is a pole of the weights only at `s = σ + ikT`. -/
theorem LadderParams.neg_zOf_ne_pole (l : LadderParams) {lam : ℝ} {s : ℂ}
    (hs : l.AvoidsWeightPoles lam s) (n : ℤ) :
    -l.zOf s ≠ (n : ℂ) - I * ((|lam| : ℝ) : ℂ) / (2 * (π : ℂ)) := by
  intro h
  apply hs (-n)
  have hT : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr l.hT.ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hz : l.zOf s * (I * l.T) = s - 1 := by
    rw [LadderParams.zOf]
    field_simp
  have h2 : l.zOf s = -((n : ℂ) - I * ((|lam| : ℝ) : ℂ) / (2 * (π : ℂ))) := by
    linear_combination -h
  rw [h2] at hz
  rw [LadderParams.sigmaOf]
  push_cast
  field_simp at hz ⊢
  linear_combination -hz + ((|lam| : ℝ) : ℂ) * (l.T : ℂ) * I_sq

theorem sign_cast_neg_one {lam : ℝ} (hlam : lam < 0) : ((Real.sign lam : ℝ) : ℂ) = -1 := by
  rw [Real.sign_of_neg hlam]; norm_num

theorem LadderParams.analyticAt_Phi_circ_neg (l : LadderParams) {lam ε : ℝ} (hlam : lam < 0)
    {s : ℂ} (hs : l.AvoidsWeightPoles lam s) :
    AnalyticAt ℂ (fun w ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf w)) s := by
  refine (Phi_circ.analyticAt_of_not_pole |lam| ε _ ?_).comp_of_eq
    (l.analyticAt_zOf (Real.sign lam : ℂ) s) rfl
  intro n
  rw [sign_cast_neg_one hlam, neg_one_mul]
  exact l.neg_zOf_ne_pole hs n

theorem LadderParams.analyticAt_Phi_star_neg (l : LadderParams) {lam ε : ℝ} (hlam : lam < 0)
    {s : ℂ} (hs : l.AvoidsWeightPoles lam s) :
    AnalyticAt ℂ (fun w ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf w)) s := by
  refine (Phi_star.analyticAt_of_not_pole |lam| ε _ ?_).comp_of_eq
    (l.analyticAt_zOf (Real.sign lam : ℂ) s) rfl
  intro n
  rw [sign_cast_neg_one hlam, neg_one_mul]
  exact l.neg_zOf_ne_pole hs n

/-- Off the vertical line `Re s = σ` there are no weight poles. -/
theorem LadderParams.avoidsWeightPoles_of_re_ne (l : LadderParams) {lam : ℝ} {s : ℂ}
    (hs : s.re ≠ l.sigmaOf lam) : l.AvoidsWeightPoles lam s := by
  intro k h
  apply hs
  rw [h]
  simp

/-- Off the horizontal lines `Im s ∈ Tℤ` there are no weight poles. -/
theorem LadderParams.avoidsWeightPoles_of_im (l : LadderParams) {lam : ℝ} {s : ℂ}
    (hs : 0 < s.im) (hs' : s.im < l.T) : l.AvoidsWeightPoles lam s := by
  intro k h
  have him : s.im = (k : ℝ) * l.T := by rw [h]; simp
  have hT := l.hT
  rcases le_or_gt k 0 with hk | hk
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    nlinarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

/-! ### The weights to the left of `σ` -/

/-- `Im(-z(s)) = -(1 - Re s)/T`, which is `≤ -|λ|/(2π) - m/T` exactly when `Re s ≤ σ - m`. -/
theorem LadderParams.im_neg_zOf_le (l : LadderParams) {lam m : ℝ} (hlam : lam < 0) {s : ℂ}
    (hs : s.re ≤ l.sigmaOf lam - m) :
    ((Real.sign lam : ℂ) * l.zOf s).im ≤ -|lam| / (2 * π) - m / l.T := by
  rw [sign_cast_neg_one hlam, neg_one_mul, Complex.neg_im, l.zOf_im]
  have hT := l.hT
  rw [LadderParams.sigmaOf] at hs
  have h1 : l.T * |lam| / (2 * π) + m ≤ 1 - s.re := by linarith
  have hkey : |lam| / (2 * π) + m / l.T ≤ (1 - s.re) / l.T := by
    have h3 := div_le_div_of_nonneg_right h1 hT.le
    have h4 : (l.T * |lam| / (2 * π) + m) / l.T = |lam| / (2 * π) + m / l.T := by
      field_simp
    linarith [h3, h4.le, h4.ge]
  have h5 : -|lam| / (2 * π) = -(|lam| / (2 * π)) := by ring
  rw [h5]
  linarith

theorem LadderParams.exists_Phi_circ_bound_left (l : LadderParams) {lam m : ℝ} (hlam : lam < 0)
    (hm : 0 < m) (ε : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ≤ l.sigmaOf lam - m →
      ‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ ≤ C := by
  have hc : -|lam| / (2 * π) - m / l.T < -|lam| / (2 * π) := by
    have : 0 < m / l.T := div_pos hm l.hT
    linarith
  obtain ⟨C, hC⟩ := ϕ_circ_bound_left |lam| |lam| ε _ hc
  exact ⟨C, fun s hs ↦ hC |lam| ⟨le_rfl, le_rfl⟩ _ (l.im_neg_zOf_le hlam hs)⟩

theorem LadderParams.exists_Phi_star_bound_left (l : LadderParams) {lam m : ℝ} (hlam : lam < 0)
    (hm : 0 < m) (ε : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ≤ l.sigmaOf lam - m →
      ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ ≤ C * (‖l.zOf s‖ + 1) := by
  have hc : -|lam| / (2 * π) - m / l.T < -|lam| / (2 * π) := by
    have : 0 < m / l.T := div_pos hm l.hT
    linarith
  have hν : 0 < |lam| := abs_pos.mpr hlam.ne
  obtain ⟨C, hC⟩ := ϕ_star_bound_left |lam| |lam| ε _ hν le_rfl hc
  refine ⟨C, fun s hs ↦ ?_⟩
  have h := hC |lam| ⟨le_rfl, le_rfl⟩ _ (l.im_neg_zOf_le hlam hs)
  have hn : ‖(Real.sign lam : ℂ) * l.zOf s‖ = ‖l.zOf s‖ := by
    rw [norm_mul, sign_cast_neg_one hlam, norm_neg, norm_one, one_mul]
  rwa [hn] at h

theorem LadderParams.sigmaOf_lt_one (l : LadderParams) {lam : ℝ} (hlam : lam < 0) :
    l.sigmaOf lam < 1 := by
  rw [LadderParams.sigmaOf]
  have : 0 < l.T * |lam| / (2 * π) := by
    have := l.hT; have := abs_pos.mpr hlam.ne; positivity
  linarith

/-- Every point of the contour misses the weight poles: the horizontal part sits at height
`δ ∈ (0, T)`, and the vertical part at `Re s = 1 > σ`. -/
theorem LadderParams.avoidsWeightPoles_of_mem_contour (l : LadderParams) {lam : ℝ}
    (hlam : lam < 0) {s : ℂ} (hs : s ∈ l.admissible_contour) : l.AvoidsWeightPoles lam s := by
  rcases hs with ⟨-, him⟩ | ⟨hre, -⟩
  · have hδ := l.hδ
    have hT := l.hT
    exact l.avoidsWeightPoles_of_im (by rw [him]; exact hδ.1) (by rw [him]; linarith [hδ.2])
  · refine l.avoidsWeightPoles_of_re_ne ?_
    rw [hre]
    exact (l.sigmaOf_lt_one hlam).ne'

theorem LadderParams.isClosed_admissible_contour (l : LadderParams) :
    IsClosed l.admissible_contour := by
  have heq : l.admissible_contour
      = {z : ℂ | z.re ≤ 1 ∧ z.im = l.δ} ∪ {z : ℂ | z.re = 1 ∧ z.im ∈ Set.Icc 0 l.δ} := rfl
  rw [heq]
  exact ((isClosed_le Complex.continuous_re continuous_const).inter
      (isClosed_eq Complex.continuous_im continuous_const)).union
    ((isClosed_eq Complex.continuous_re continuous_const).inter
      (isClosed_Icc.preimage Complex.continuous_im))

/-- The part of the contour to the right of `Re s = a` is compact. -/
theorem LadderParams.isCompact_contour_right (l : LadderParams) (a : ℝ) :
    IsCompact ({z : ℂ | a ≤ z.re} ∩ l.admissible_contour) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨(isClosed_le continuous_const Complex.continuous_re).inter
    l.isClosed_admissible_contour, ?_⟩
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨|a| + 1 + l.δ, fun z hz ↦ ?_⟩
  obtain ⟨ha, hc⟩ := hz
  have hδ := l.hδ
  have hre : |z.re| ≤ |a| + 1 := by
    have h1 : z.re ≤ 1 := by rcases hc with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
    have ha' : a ≤ z.re := ha
    rw [abs_le]
    constructor <;> linarith [neg_abs_le a, le_abs_self a]
  have him : |z.im| ≤ l.δ := by
    rcases hc with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h, abs_of_pos hδ.1]
    · rw [abs_of_nonneg h.1]; exact h.2
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |a| + 1 + l.δ := by linarith

/-! ### Boundedness on the ladder and the contour -/

theorem LadderParams.isBoundedNoPolesOn_Phi_circ_mul_L_neg (l : LadderParams) {F : ℂ → ℂ}
    {lam ε x₀ m : ℝ} (hlam : lam < 0) (hm : 0 < m)
    (hL : ∀ n, 1 ≤ n → l.σ n ≤ l.sigmaOf lam - m)
    (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.L) :
    IsBoundedNoPolesOn
      (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x₀ : ℂ) ^ s) l.L := by
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  obtain ⟨C, hC⟩ := l.exists_Phi_circ_bound_left hlam hm ε
  have hre : ∀ z ∈ l.L, z.re ≤ l.sigmaOf lam - m := by
    rintro z ⟨n, hn, hz, -⟩
    rw [hz]
    exact hL n hn
  simp only [mul_assoc]
  refine hF_bdd.analytic_mul (C := C)
    (fun z hz ↦ (hF_mero z (l.L_subset_R hz)).mul (meromorphicAt_rpow hx₀_pos z))
    (fun z hz ↦ ?_) (fun z hz ↦ hC z (hre z hz))
  refine l.analyticAt_Phi_circ_neg hlam (l.avoidsWeightPoles_of_re_ne ?_)
  have := hre z hz
  linarith

theorem LadderParams.isBoundedNoPolesOn_Phi_star_mul_L_neg (l : LadderParams) {F : ℂ → ℂ}
    {lam ε x₀ m : ℝ} (hlam : lam < 0) (hm : 0 < m)
    (hL : ∀ n, 1 ≤ n → l.σ n ≤ l.sigmaOf lam - m)
    (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.L)
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) l.L) :
    IsBoundedNoPolesOn
      (fun s ↦ (Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
        F s * (x₀ : ℂ) ^ s) l.L := by
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  obtain ⟨C, hC⟩ := l.exists_Phi_star_bound_left hlam hm ε
  have hre : ∀ z ∈ l.L, z.re ≤ l.sigmaOf lam - m := by
    rintro z ⟨n, hn, hz, -⟩
    rw [hz]
    exact hL n hn
  have hwh : IsBoundedNoPolesOn (fun s ↦ l.zOf s * (F s * (x₀ : ℂ) ^ s)) l.L := by
    have heqw : (fun s ↦ l.zOf s * (F s * (x₀ : ℂ) ^ s))
        = (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) := by funext s; ring
    rw [heqw]; exact hFw_bdd
  have heq :
      (fun s ↦ (Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
          F s * (x₀ : ℂ) ^ s)
        = (fun s ↦ ((Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) *
          (F s * (x₀ : ℂ) ^ s)) := by funext s; ring
  rw [heq]
  refine hF_bdd.linear_mul (w := l.zOf) (C := C) hwh
    (fun z hz ↦ (hF_mero z (l.L_subset_R hz)).mul (meromorphicAt_rpow hx₀_pos z))
    (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · refine analyticAt_const.mul
      (l.analyticAt_Phi_star_neg hlam (l.avoidsWeightPoles_of_re_ne ?_))
    have := hre z hz
    linarith
  · have hs1 : ‖((Real.sign lam : ℝ) : ℂ)‖ = 1 := by rw [sign_cast_neg_one hlam]; simp
    rw [norm_mul, hs1, one_mul]
    exact hC z (hre z hz)

theorem LadderParams.isBoundedNoPolesOn_Phi_circ_mul_contour_neg (l : LadderParams) {F : ℂ → ℂ}
    {lam ε x₀ : ℝ} (hlam : lam < 0)
    (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    IsBoundedNoPolesOn
      (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x₀ : ℂ) ^ s)
      l.admissible_contour := by
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  obtain ⟨C₁, hC₁⟩ := l.exists_Phi_circ_bound_left (m := 1) hlam one_pos ε
  have hcont : ContinuousOn (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s))
      ({z : ℂ | l.sigmaOf lam - 1 ≤ z.re} ∩ l.admissible_contour) := fun z hz ↦
    (l.analyticAt_Phi_circ_neg hlam
      (l.avoidsWeightPoles_of_mem_contour hlam hz.2)).continuousAt.continuousWithinAt
  obtain ⟨C₂, hC₂⟩ :=
    (l.isCompact_contour_right (l.sigmaOf lam - 1)).exists_bound_of_continuousOn hcont
  simp only [mul_assoc]
  refine hF_bdd.analytic_mul (C := max C₁ C₂)
    (fun z hz ↦ (hF_mero z (l.admissible_contour_subset_R hz)).mul
      (meromorphicAt_rpow hx₀_pos z))
    (fun z hz ↦ l.analyticAt_Phi_circ_neg hlam (l.avoidsWeightPoles_of_mem_contour hlam hz))
    (fun z hz ↦ ?_)
  rcases le_or_gt z.re (l.sigmaOf lam - 1) with h | h
  · exact le_trans (hC₁ z h) (le_max_left _ _)
  · exact le_trans (hC₂ z ⟨h.le, hz⟩) (le_max_right _ _)

theorem LadderParams.isBoundedNoPolesOn_Phi_star_mul_contour_neg (l : LadderParams) {F : ℂ → ℂ}
    {lam ε x₀ : ℝ} (hlam : lam < 0)
    (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    IsBoundedNoPolesOn
      (fun s ↦ (Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
        F s * (x₀ : ℂ) ^ s) l.admissible_contour := by
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  obtain ⟨C₁, hC₁⟩ := l.exists_Phi_star_bound_left (m := 1) hlam one_pos ε
  have hcont : ContinuousOn (fun s ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s))
      ({z : ℂ | l.sigmaOf lam - 1 ≤ z.re} ∩ l.admissible_contour) := fun z hz ↦
    (l.analyticAt_Phi_star_neg hlam
      (l.avoidsWeightPoles_of_mem_contour hlam hz.2)).continuousAt.continuousWithinAt
  obtain ⟨C₂, hC₂⟩ :=
    (l.isCompact_contour_right (l.sigmaOf lam - 1)).exists_bound_of_continuousOn hcont
  have hwh : IsBoundedNoPolesOn (fun s ↦ l.zOf s * (F s * (x₀ : ℂ) ^ s))
      l.admissible_contour := by
    have heqw : (fun s ↦ l.zOf s * (F s * (x₀ : ℂ) ^ s))
        = (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) := by funext s; ring
    rw [heqw]; exact hFw_bdd
  have heq :
      (fun s ↦ (Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
          F s * (x₀ : ℂ) ^ s)
        = (fun s ↦ ((Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) *
          (F s * (x₀ : ℂ) ^ s)) := by funext s; ring
  rw [heq]
  refine hF_bdd.linear_mul (w := l.zOf) (C := max |C₁| |C₂|) hwh
    (fun z hz ↦ (hF_mero z (l.admissible_contour_subset_R hz)).mul
      (meromorphicAt_rpow hx₀_pos z))
    (fun z hz ↦ analyticAt_const.mul
      (l.analyticAt_Phi_star_neg hlam (l.avoidsWeightPoles_of_mem_contour hlam hz)))
    (fun z hz ↦ ?_)
  have hs1 : ‖((Real.sign lam : ℝ) : ℂ)‖ = 1 := by rw [sign_cast_neg_one hlam]; simp
  rw [norm_mul, hs1, one_mul]
  have hn1 : (1 : ℝ) ≤ ‖l.zOf z‖ + 1 := by linarith [norm_nonneg (l.zOf z)]
  have hpos : (0 : ℝ) ≤ ‖l.zOf z‖ + 1 := by linarith
  rcases le_or_gt z.re (l.sigmaOf lam - 1) with h | h
  · calc ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf z)‖ ≤ C₁ * (‖l.zOf z‖ + 1) := hC₁ z h
      _ ≤ |C₁| * (‖l.zOf z‖ + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) hpos
      _ ≤ max |C₁| |C₂| * (‖l.zOf z‖ + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  · calc ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf z)‖ ≤ C₂ := hC₂ z ⟨h.le, hz⟩
      _ ≤ |C₂| := le_abs_self _
      _ ≤ |C₂| * (‖l.zOf z‖ + 1) := le_mul_of_one_le_right (abs_nonneg _) hn1
      _ ≤ max |C₁| |C₂| * (‖l.zOf z‖ + 1) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos

/-! ### The boundary of `R`, and the two removable singularities on it

On the top and bottom edges the weights `Φ^∘(-z(s))` and `Φ^⋆(-z(s))` each have a pole at
`s = σ ± iT`, but `Φ_λ` does not. The cancellation is the shift identity
`Φ^∘(v - 1) - Φ^⋆(v - 1) = -Φ^⋆(v)`, which near `σ + iT` writes `Φ_λ(z(s))` as `-Φ^⋆(1 - z(s))`, and
`Φ^⋆` is analytic at `1 - z(σ + iT) = -i|λ|/(2π)` (its only pole-free lattice point). -/


/-- `2πi z(w) + |λ| ≠ 0` off the real axis: its imaginary part is `2π Im w / T`. -/
theorem LadderParams.two_pi_I_zOf_add_ne (l : LadderParams) (lam : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    2 * (π : ℂ) * I * l.zOf w + ((|lam| : ℝ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hzr := l.zOf_re w
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.zero_im, Complex.mul_re] at him
  rw [hzr] at him
  have hT := l.hT
  have hπ := Real.pi_pos
  have : 2 * π * (w.im / l.T) ≠ 0 := by
    have : w.im / l.T ≠ 0 := div_ne_zero hw hT.ne'
    positivity
  apply this
  linarith

/-- `-z(s) = (1 - z(s)) - 1`: the shift identity in the upper half-plane, away from `σ` and
`σ + iT`. -/
theorem LadderParams.Phi_lambda_neg_eq_top (l : LadderParams) {lam ε : ℝ} (hlam : lam < 0)
    {w : ℂ} (hw_im : 0 < w.im)
    (hw1 : w ≠ ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I) :
    Phi_lambda lam ε (l.zOf w) = -Phi_star |lam| ε (1 - l.zOf w) := by
  have hν : 0 < |lam| := abs_pos.mpr hlam.ne
  have hT : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr l.hT.ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hre : 0 < (l.zOf w).re := by rw [l.zOf_re]; exact div_pos hw_im l.hT
  have hz : l.zOf w * (I * l.T) = w - 1 := by
    rw [LadderParams.zOf]; field_simp
  have hw : -2 * (π : ℂ) * I * (1 - l.zOf w) + ((|lam| : ℝ) : ℂ) ≠ 0 := by
    intro h
    apply hw1
    rw [LadderParams.sigmaOf]
    push_cast
    have h2 : l.zOf w = 1 - ((|lam| : ℝ) : ℂ) / (2 * π * I) := by
      field_simp
      linear_combination h
    rw [h2] at hz
    field_simp at hz
    have h3 : (2 * (π : ℂ)) * (w - (1 - (l.T : ℂ) * ((|lam| : ℝ) : ℂ) / (2 * π) + (l.T : ℂ) * I))
        = 0 := by
      have e : (2 * (π : ℂ)) * (w - (1 - (l.T : ℂ) * ((|lam| : ℝ) : ℂ) / (2 * π) + (l.T : ℂ) * I))
          = 2 * π * (w - 1) + (l.T : ℂ) * ((|lam| : ℝ) : ℂ) - 2 * π * l.T * I := by
        field_simp
        ring
      rw [e]
      linear_combination -hz
    have h4 := (mul_eq_zero.mp h3).resolve_left (by simp [hπ])
    linear_combination h4
  have hwm : -2 * (π : ℂ) * I * ((1 - l.zOf w) - ((1 : ℤ) : ℂ)) + ((|lam| : ℝ) : ℂ) ≠ 0 := by
    rw [show -2 * (π : ℂ) * I * ((1 - l.zOf w) - ((1 : ℤ) : ℂ)) + ((|lam| : ℝ) : ℂ)
        = 2 * (π : ℂ) * I * l.zOf w + ((|lam| : ℝ) : ℂ) by push_cast; ring]
    exact l.two_pi_I_zOf_add_ne lam hw_im.ne'
  rw [Phi_lambda, sign_cast_neg_one hlam, Real.sign_of_pos hre]
  have harg : -1 * l.zOf w = (1 - l.zOf w) - ((1 : ℤ) : ℂ) := by push_cast; ring
  have hc : Phi_circ |lam| ε ((1 - l.zOf w) - ((1 : ℤ) : ℂ)) = Phi_circ |lam| ε (1 - l.zOf w) := by
    have h := Phi_circ_periodic |lam| ε ((1 - l.zOf w) - ((1 : ℤ) : ℂ))
    rw [show (1 - l.zOf w) - ((1 : ℤ) : ℂ) + 1 = 1 - l.zOf w by push_cast; ring] at h
    exact h.symm
  have hs := phi_star_affine_periodic |lam| ε hν (1 - l.zOf w) 1 hw hwm
  rw [harg, hc, hs]
  push_cast
  ring

/-- The bottom-edge version: in the lower half-plane `Φ_λ(z(s)) = Φ^⋆(-1 - z(s))`. -/
theorem LadderParams.Phi_lambda_neg_eq_bot (l : LadderParams) {lam ε : ℝ} (hlam : lam < 0)
    {w : ℂ} (hw_im : w.im < 0)
    (hw1 : w ≠ ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I) :
    Phi_lambda lam ε (l.zOf w) = Phi_star |lam| ε (-1 - l.zOf w) := by
  have hν : 0 < |lam| := abs_pos.mpr hlam.ne
  have hT : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr l.hT.ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hre : (l.zOf w).re < 0 := by rw [l.zOf_re]; exact div_neg_of_neg_of_pos hw_im l.hT
  have hz : l.zOf w * (I * l.T) = w - 1 := by
    rw [LadderParams.zOf]; field_simp
  have hw : -2 * (π : ℂ) * I * (-1 - l.zOf w) + ((|lam| : ℝ) : ℂ) ≠ 0 := by
    intro h
    apply hw1
    rw [LadderParams.sigmaOf]
    push_cast
    have h2 : l.zOf w = -1 - ((|lam| : ℝ) : ℂ) / (2 * π * I) := by
      field_simp
      linear_combination h
    rw [h2] at hz
    field_simp at hz
    have h3 : (2 * (π : ℂ)) * (w - (1 - (l.T : ℂ) * ((|lam| : ℝ) : ℂ) / (2 * π) - (l.T : ℂ) * I))
        = 0 := by
      have e : (2 * (π : ℂ)) * (w - (1 - (l.T : ℂ) * ((|lam| : ℝ) : ℂ) / (2 * π) - (l.T : ℂ) * I))
          = 2 * π * (w - 1) + (l.T : ℂ) * ((|lam| : ℝ) : ℂ) + 2 * π * l.T * I := by
        field_simp
        ring
      rw [e]
      linear_combination -hz
    have h4 := (mul_eq_zero.mp h3).resolve_left (by simp [hπ])
    linear_combination h4
  have hwm : -2 * (π : ℂ) * I * ((-1 - l.zOf w) - ((-1 : ℤ) : ℂ)) + ((|lam| : ℝ) : ℂ) ≠ 0 := by
    rw [show -2 * (π : ℂ) * I * ((-1 - l.zOf w) - ((-1 : ℤ) : ℂ)) + ((|lam| : ℝ) : ℂ)
        = 2 * (π : ℂ) * I * l.zOf w + ((|lam| : ℝ) : ℂ) by push_cast; ring]
    exact l.two_pi_I_zOf_add_ne lam hw_im.ne
  rw [Phi_lambda, sign_cast_neg_one hlam, Real.sign_of_neg hre]
  have harg : -1 * l.zOf w = (-1 - l.zOf w) - ((-1 : ℤ) : ℂ) := by push_cast; ring
  have hc : Phi_circ |lam| ε ((-1 - l.zOf w) - ((-1 : ℤ) : ℂ))
      = Phi_circ |lam| ε (-1 - l.zOf w) := by
    rw [show (-1 - l.zOf w) - ((-1 : ℤ) : ℂ) = (-1 - l.zOf w) + 1 by push_cast; ring]
    exact Phi_circ_periodic |lam| ε (-1 - l.zOf w)
  have hs := phi_star_affine_periodic |lam| ε hν (-1 - l.zOf w) (-1) hw hwm
  rw [harg, hc, hs]
  push_cast
  ring

/-- The order of `Φ_λ(z(s)) · h(s)` is `≥ 0` at a point where both weights are continuous and `h`
has order `≥ 0`. `meromorphicOrderAt_Phi_lambda_mul_nonneg` with the sign hypothesis replaced by
what it was used for. -/
theorem meromorphicOrderAt_Phi_lambda_mul_nonneg_of_continuousAt (l : LadderParams)
    {h : ℂ → ℂ} {lam ε : ℝ} {z : ℂ}
    (hφc : ContinuousAt (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) z)
    (hφs : ContinuousAt (fun s ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) z)
    (hh_mero : MeromorphicAt h z) (hh_ord : 0 ≤ meromorphicOrderAt h z) :
    0 ≤ meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * h s) z := by
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hh_mero hh_ord
  set L : ℝ := (‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf z)‖ +
      ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf z)‖) * ‖c‖ with hLdef
  have hg : Filter.Tendsto
      (fun s ↦ (‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ +
        ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖) * ‖h s‖)
      (nhdsWithin z {z}ᶜ) (nhds L) :=
    ((((hφc.norm).tendsto.mono_left nhdsWithin_le_nhds).add
      ((hφs.norm).tendsto.mono_left nhdsWithin_le_nhds)).mul hc.norm)
  refine meromorphicOrderAt_nonneg_of_eventually_bounded (M := L + 1) ?_
  filter_upwards [hg.eventually_lt_const (lt_add_one L)] with s hs
  calc ‖Phi_lambda lam ε (l.zOf s) * h s‖
      = ‖Phi_lambda lam ε (l.zOf s)‖ * ‖h s‖ := norm_mul _ _
    _ ≤ (‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ +
          ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖) * ‖h s‖ :=
        mul_le_mul_of_nonneg_right (norm_Phi_lambda_le_sum lam ε (l.zOf s)) (norm_nonneg _)
    _ ≤ L + 1 := le_of_lt hs

/-- **The removable singularity at `σ + iT`.** -/
theorem LadderParams.meromorphicOrderAt_Phi_lambda_mul_top_neg (l : LadderParams)
    {h : ℂ → ℂ} {lam ε : ℝ} (hlam : lam < 0)
    (hh_mero : MeromorphicAt h (((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I))
    (hh_ord : 0 ≤ meromorphicOrderAt h (((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I)) :
    0 ≤ meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * h s)
      (((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I) := by
  set z₀ : ℂ := ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I with hz₀
  have hz₀im : z₀.im = l.T := by simp [hz₀]
  have hzA : AnalyticAt ℂ l.zOf z₀ := by simpa using l.analyticAt_zOf 1 z₀
  have hg : AnalyticAt ℂ (fun w ↦ -Phi_star |lam| ε (1 - l.zOf w)) z₀ := by
    refine ((Phi_star.analyticAt_of_not_pole_nz |lam| ε (1 - l.zOf z₀) ?_).comp_of_eq
      (analyticAt_const.sub hzA) rfl).neg
    intro n hn heq
    have hL : (1 - l.zOf z₀).re = 0 := by
      rw [Complex.sub_re, Complex.one_re, l.zOf_re, hz₀im, div_self l.hT.ne']; ring
    have heq' : 1 - l.zOf z₀ = ((n : ℝ) : ℂ) + ((-(|lam| / (2 * π)) : ℝ) : ℂ) * I := by
      rw [heq]; push_cast; ring
    have hre := congrArg Complex.re heq'
    rw [hL] at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one] at hre
    exact hn (by exact_mod_cast hre.symm)
  have hopen : ∀ᶠ w in nhds z₀, 0 < w.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (by show 0 < z₀.im; rw [hz₀im]; exact l.hT)
  have hev : (fun s ↦ Phi_lambda lam ε (l.zOf s) * h s) =ᶠ[nhdsWithin z₀ {z₀}ᶜ]
      (fun s ↦ -Phi_star |lam| ε (1 - l.zOf s) * h s) := by
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with w hw hw'
    rw [l.Phi_lambda_neg_eq_top hlam hw hw']
  rw [meromorphicOrderAt_congr hev,
    show (fun s ↦ -Phi_star |lam| ε (1 - l.zOf s) * h s)
      = (fun s ↦ -Phi_star |lam| ε (1 - l.zOf s)) * h from rfl,
    meromorphicOrderAt_mul hg.meromorphicAt hh_mero]
  exact add_nonneg hg.meromorphicOrderAt_nonneg hh_ord

/-- **The removable singularity at `σ - iT`.** -/
theorem LadderParams.meromorphicOrderAt_Phi_lambda_mul_bot_neg (l : LadderParams)
    {h : ℂ → ℂ} {lam ε : ℝ} (hlam : lam < 0)
    (hh_mero : MeromorphicAt h (((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I))
    (hh_ord : 0 ≤ meromorphicOrderAt h (((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I)) :
    0 ≤ meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * h s)
      (((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I) := by
  set z₀ : ℂ := ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I with hz₀
  have hz₀im : z₀.im = -l.T := by simp [hz₀]
  have hzA : AnalyticAt ℂ l.zOf z₀ := by simpa using l.analyticAt_zOf 1 z₀
  have hg : AnalyticAt ℂ (fun w ↦ Phi_star |lam| ε (-1 - l.zOf w)) z₀ := by
    refine (Phi_star.analyticAt_of_not_pole_nz |lam| ε (-1 - l.zOf z₀) ?_).comp_of_eq
      (analyticAt_const.sub hzA) rfl
    intro n hn heq
    have hL : (-1 - l.zOf z₀).re = 0 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re, l.zOf_re, hz₀im, neg_div,
        div_self l.hT.ne']; ring
    have heq' : -1 - l.zOf z₀ = ((n : ℝ) : ℂ) + ((-(|lam| / (2 * π)) : ℝ) : ℂ) * I := by
      rw [heq]; push_cast; ring
    have hre := congrArg Complex.re heq'
    rw [hL] at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one] at hre
    exact hn (by exact_mod_cast hre.symm)
  have hopen : ∀ᶠ w in nhds z₀, w.im < 0 :=
    (isOpen_lt Complex.continuous_im continuous_const).mem_nhds
      (by show z₀.im < 0; rw [hz₀im]; exact neg_lt_zero.mpr l.hT)
  have hev : (fun s ↦ Phi_lambda lam ε (l.zOf s) * h s) =ᶠ[nhdsWithin z₀ {z₀}ᶜ]
      (fun s ↦ Phi_star |lam| ε (-1 - l.zOf s) * h s) := by
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with w hw hw'
    rw [l.Phi_lambda_neg_eq_bot hlam hw hw']
  rw [meromorphicOrderAt_congr hev,
    show (fun s ↦ Phi_star |lam| ε (-1 - l.zOf s) * h s)
      = (fun s ↦ Phi_star |lam| ε (-1 - l.zOf s)) * h from rfl,
    meromorphicOrderAt_mul hg.meromorphicAt hh_mero]
  exact add_nonneg hg.meromorphicOrderAt_nonneg hh_ord

/-- The right edge of `R` is compact. -/
theorem LadderParams.isCompact_right_edge (l : LadderParams) :
    IsCompact {z : ℂ | z.re = 1 ∧ |z.im| ≤ l.T} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨(isClosed_eq Complex.continuous_re continuous_const).inter
    (isClosed_le Complex.continuous_im.abs continuous_const), ?_⟩
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1 + l.T, fun z hz ↦ ?_⟩
  obtain ⟨hre, him⟩ := hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 + l.T := by rw [hre, abs_one]; linarith

/-- **`Φ_λ(z(s))` grows at most linearly on `∂R`**, for `λ < 0`. Away from `σ ± iT` this is the
edge lemmas and a compactness bound on the right edge; the two exceptional points contribute
whatever finite (junk) value `Φ_λ` takes there. -/
theorem LadderParams.exists_Phi_lambda_bound_boundary_neg (l : LadderParams) {lam ε : ℝ}
    (hlam : lam < 0) (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, ∀ s ∈ l.Rboundary, ‖Phi_lambda lam ε (l.zOf s)‖ ≤ C * (‖l.zOf s‖ + 1) := by
  have hT := l.hT
  have hcont : ContinuousOn
      (fun s ↦ ‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ +
        ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖)
      {z : ℂ | z.re = 1 ∧ |z.im| ≤ l.T} := fun z hz ↦ by
    have hav : l.AvoidsWeightPoles lam z :=
      l.avoidsWeightPoles_of_re_ne (by rw [hz.1]; exact (l.sigmaOf_lt_one hlam).ne')
    exact ((l.analyticAt_Phi_circ_neg (ε := ε) hlam hav).continuousAt.norm.add
      (l.analyticAt_Phi_star_neg (ε := ε) hlam hav).continuousAt.norm).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := l.isCompact_right_edge.exists_bound_of_continuousOn hcont
  set Kp : ℝ := ‖Phi_lambda lam ε (l.zOf (((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I))‖
  set Km : ℝ := ‖Phi_lambda lam ε (l.zOf (((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I))‖
  set C : ℝ := max 1 (max |C₀| (max Kp Km)) with hC
  refine ⟨C, fun s hs ↦ ?_⟩
  have hn1 : (1 : ℝ) ≤ ‖l.zOf s‖ + 1 := by linarith [norm_nonneg (l.zOf s)]
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCle : C ≤ C * (‖l.zOf s‖ + 1) := le_mul_of_one_le_right (by linarith) hn1
  have hyz : (1 - s.re) / l.T ≤ ‖l.zOf s‖ := by
    rw [← l.zOf_im]
    exact le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  rcases hs with ⟨hre, him⟩ | ⟨hre, him⟩
  · have h1 := norm_Phi_lambda_le_sum lam ε (l.zOf s)
    have h2 := hC₀ s ⟨hre, him⟩
    rw [Real.norm_eq_abs] at h2
    have h3 : |C₀| ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith [le_abs_self (‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ +
        ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖), le_abs_self C₀]
  · have hy : 0 ≤ (1 - s.re) / l.T := div_nonneg (by linarith) hT.le
    rcases (abs_eq hT.le).mp him with hTi | hTi
    · by_cases hsr : s.re = l.sigmaOf lam
      · have hs_eq : s = ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I :=
          Complex.ext (by simp [hsr]) (by simp [hTi])
        have hK : Kp ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_max_right _ _)
        rw [hs_eq]
        rw [hs_eq] at hCle
        linarith
      · have hs_eq : s = (s.re : ℂ) + (l.T : ℂ) * I := Complex.ext (by simp) (by simp [hTi])
        have hpole : (1 - s.re) / l.T ≠ |lam| / (2 * π) := by
          intro h
          apply hsr
          rw [LadderParams.sigmaOf]
          field_simp at h ⊢
          linarith
        have hb : ‖Phi_lambda lam ε (l.zOf s)‖ ≤ (1 - s.re) / l.T := by
          conv_lhs => rw [hs_eq, l.zOf_top_hray]
          exact norm_Phi_lambda_one_add_I_mul_le_of_neg lam ε _ hlam hε hy hpole
        nlinarith [hb, hyz, hC1]
    · by_cases hsr : s.re = l.sigmaOf lam
      · have hs_eq : s = ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I :=
          Complex.ext (by simp [hsr]) (by simp [hTi])
        have hK : Km ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_max_right _ _)
        rw [hs_eq]
        rw [hs_eq] at hCle
        linarith
      · have hs_eq : s = (s.re : ℂ) - (l.T : ℂ) * I := Complex.ext (by simp) (by simp [hTi])
        have hpole : (1 - s.re) / l.T ≠ |lam| / (2 * π) := by
          intro h
          apply hsr
          rw [LadderParams.sigmaOf]
          field_simp at h ⊢
          linarith
        have hb : ‖Phi_lambda lam ε (l.zOf s)‖ ≤ (1 - s.re) / l.T := by
          conv_lhs => rw [hs_eq, l.zOf_bot_hray]
          exact norm_Phi_lambda_neg_one_add_I_mul_le_of_neg lam ε _ hlam hε hy hpole
        nlinarith [hb, hyz, hC1]

/-- **`lemma_5_1`'s boundary hypothesis for `λ < 0`.** -/
theorem LadderParams.isBoundedNoPolesOn_Phi_lambda_mul_boundary_neg (l : LadderParams)
    {F : ℂ → ℂ} {lam ε x₀ : ℝ} (hlam : lam < 0) (hε : ε = 1 ∨ ε = -1)
    (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) l.Rboundary) :
    IsBoundedNoPolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x₀ : ℂ) ^ s)
      l.Rboundary := by
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  obtain ⟨Cl, hCl⟩ := l.exists_Phi_lambda_bound_boundary_neg hlam hε
  obtain ⟨Mh, hMh⟩ := hF_bdd
  obtain ⟨Mwh, hMwh⟩ := hFw_bdd
  refine ⟨|Cl| * Mwh + |Cl| * Mh, fun z hz ↦ ⟨?_, ?_⟩⟩
  · have hwh_z : ‖l.zOf z‖ * ‖F z * (x₀ : ℂ) ^ z‖ ≤ Mwh := by
      have h := (hMwh z hz).1
      change ‖l.zOf z * F z * (x₀ : ℂ) ^ z‖ ≤ Mwh at h
      rwa [mul_assoc, norm_mul] at h
    change ‖Phi_lambda lam ε (l.zOf z) * F z * (x₀ : ℂ) ^ z‖ ≤ |Cl| * Mwh + |Cl| * Mh
    rw [mul_assoc]
    exact norm_mul_le_of_linear_growth (hCl z hz) (hMh z hz).1 hwh_z
  · have hmero : MeromorphicAt (fun s ↦ F s * (x₀ : ℂ) ^ s) z :=
      (hF_mero z (l.Rboundary_subset_R hz)).mul (meromorphicAt_rpow hx₀_pos z)
    have hord := (hMh z hz).2
    have heq : (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x₀ : ℂ) ^ s)
        = (fun s ↦ Phi_lambda lam ε (l.zOf s) * (F s * (x₀ : ℂ) ^ s)) := by
      funext s; ring
    rw [heq]
    by_cases htop : z = ((l.sigmaOf lam : ℝ) : ℂ) + (l.T : ℂ) * I
    · subst htop
      exact l.meromorphicOrderAt_Phi_lambda_mul_top_neg hlam hmero hord
    by_cases hbot : z = ((l.sigmaOf lam : ℝ) : ℂ) - (l.T : ℂ) * I
    · subst hbot
      exact l.meromorphicOrderAt_Phi_lambda_mul_bot_neg hlam hmero hord
    have hre : z.re ≠ l.sigmaOf lam := by
      intro hzr
      rcases hz with ⟨hre1, -⟩ | ⟨-, him⟩
      · exact (l.sigmaOf_lt_one hlam).ne' (hre1.symm.trans hzr)
      · rcases (abs_eq l.hT.le).mp him with hTi | hTi
        · exact htop (Complex.ext (by simp [hzr]) (by simp [hTi]))
        · exact hbot (Complex.ext (by simp [hzr]) (by simp [hTi]))
    have hav := l.avoidsWeightPoles_of_re_ne (lam := lam) hre
    exact meromorphicOrderAt_Phi_lambda_mul_nonneg_of_continuousAt l
      (l.analyticAt_Phi_circ_neg hlam hav).continuousAt
      (l.analyticAt_Phi_star_neg hlam hav).continuousAt hmero hord

/-! ### Proposition 5.2 for `λ < 0` -/

section Proposition52Neg

variable {l : LadderParams} {F : ℂ → ℂ} {lam ε x₀ x m : ℝ}

/-- **`prop_5_2_a` for `λ < 0`.** The same identity; only the boundedness side conditions change,
and they are supplied by the lemmas above. The ladder columns must lie a fixed distance `m` to the
left of `σ`, which for `A = -ζ'/ζ` (columns `1 - 2n`) holds for every `σ ∈ [0, 1)`. -/
theorem prop_5_2_a_neg
    (hF_mero : MeromorphicOn F l.R)
    (hF_symm : ConjSymm F)
    (hlam : lam < 0) (hε : ε = 1 ∨ ε = -1)
    (hm : 0 < m) (hL : ∀ n, 1 ≤ n → l.σ n ≤ l.sigmaOf lam - m)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC |
        meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z < 0}.Finite)
    (hsimple : HasSimplePolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s)
      (l.Rpos ∪ l.RposBar))
    (hsimple_circ :
        HasSimplePolesOn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.R) :
    (2 * (π : ℂ) * Complex.I)⁻¹ *
        l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) +
        (↑(π⁻¹ * (l.intC (fun s ↦ (Real.sign lam : ℂ) *
            Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ) +
        sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) +
        l.sumResiduesLim
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.RC := by
  refine lemma_5_1
    (G := fun s ↦ Phi_lambda lam ε (l.zOf s) * F s)
    (G_circ := fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s)
    (G_star := fun s ↦ (Real.sign lam : ℂ) *
        Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s)
    ?hG ?hGc_mero ?hGs_mero ?hGs_symm ?hGc_symm hx₀ ?hG_bdd ?hGc_L ?hGc_contour
    ?hGs_L ?hGs_contour hx ?hfin ?hsimple ?hsimple_circ
  case hfin => exact hfin
  case hsimple => exact hsimple
  case hsimple_circ => exact hsimple_circ
  -- remaining genuine subgoals (to be discharged):
  case hG =>
    intro s
    simp only [Phi_lambda, l.sign_zOf_re]
    ring
  case hGc_mero =>
    intro z hz
    refine MeromorphicAt.mul ?_ (hF_mero z hz)
    exact (Phi_circ.meromorphic |lam| ε _).comp_analyticAt (l.analyticAt_zOf _ z)
  case hGs_mero =>
    intro z hz
    refine MeromorphicAt.mul ?_ (hF_mero z hz)
    exact (MeromorphicAt.const (Real.sign lam : ℂ) z).mul
      ((Phi_star.meromorphic |lam| ε _).comp_analyticAt (l.analyticAt_zOf _ z))
  case hGs_symm =>
    intro s
    simp only []
    rw [l.zOf_conj, hF_symm,
      show (Real.sign lam : ℂ) * -(starRingEnd ℂ (l.zOf s)) =
          -(starRingEnd ℂ ((Real.sign lam : ℂ) * l.zOf s)) by
        rw [map_mul, Complex.conj_ofReal]; ring,
      Phi_star_conj_neg, map_mul, map_mul, Complex.conj_ofReal]
    ring
  case hGc_symm =>
    intro s
    simp only []
    have hPhi : Phi_circ |lam| ε
        (-(starRingEnd ℂ ((Real.sign lam : ℂ) * l.zOf s))) =
        starRingEnd ℂ (Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) := by
      unfold Phi_circ
      simp only [map_mul, map_add, map_div₀, Complex.conj_ofReal, neg_mul, mul_neg,
        neg_neg, coth_conj, map_one, map_ofNat, Complex.conj_I, map_neg]
    rw [l.zOf_conj, hF_symm,
      show (Real.sign lam : ℂ) * -(starRingEnd ℂ (l.zOf s)) =
          -(starRingEnd ℂ ((Real.sign lam : ℂ) * l.zOf s)) by
        rw [map_mul, Complex.conj_ofReal]
        ring,
      hPhi, map_mul]
  case hG_bdd =>
    exact l.isBoundedNoPolesOn_Phi_lambda_mul_boundary_neg hlam hε hx₀ hF_mero
      (hF_bdd.mono (Set.subset_union_left.trans Set.subset_union_left))
      (hFw_bdd.mono (Set.subset_union_left.trans Set.subset_union_left))
  case hGc_L =>
    exact l.isBoundedNoPolesOn_Phi_circ_mul_L_neg hlam hm hL hx₀ hF_mero
      (hF_bdd.mono Set.subset_union_right)
  case hGc_contour =>
    exact l.isBoundedNoPolesOn_Phi_circ_mul_contour_neg hlam hx₀ hF_mero
      (hF_bdd.mono (Set.subset_union_right.trans Set.subset_union_left))
  case hGs_L =>
    exact l.isBoundedNoPolesOn_Phi_star_mul_L_neg hlam hm hL hx₀ hF_mero
      (hF_bdd.mono Set.subset_union_right) (hFw_bdd.mono Set.subset_union_right)
  case hGs_contour =>
    exact l.isBoundedNoPolesOn_Phi_star_mul_contour_neg hlam hx₀ hF_mero
      (hF_bdd.mono (Set.subset_union_right.trans Set.subset_union_left))
      (hFw_bdd.mono (Set.subset_union_right.trans Set.subset_union_left))

/-- **Proposition 5.2 for `λ < 0`.** -/
theorem prop_5_2_neg
    (hF_mero : MeromorphicOn F l.R)
    (hF_symm : ConjSymm F)
    (hlam : lam < 0) (hε : ε = 1 ∨ ε = -1)
    (hm : 0 < m) (hL : ∀ n, 1 ≤ n → l.σ n ≤ l.sigmaOf lam - m)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC |
        meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z < 0}.Finite)
    (hsimple : HasSimplePolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s)
      (l.Rpos ∪ l.RposBar))
    (hsimple_circ :
        HasSimplePolesOn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.R) :
    ‖(2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) -
        sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) -
        l.sumResiduesLim
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.RC‖ ≤
      (1 / (2 * π)) *
        ((1 / l.T) *
            ((∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t + l.T * Complex.I)‖ * x ^ (1 - t)) +
              ∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t - l.T * Complex.I)‖ * x ^ (1 - t)) +
          2 * ‖l.intC (fun s ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)‖) := by
  have hLHS :
      (2 * (π : ℂ) * Complex.I)⁻¹ *
            l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) -
          sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) -
          l.sumResiduesLim
            (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.RC =
        (2 * (π : ℂ) * Complex.I)⁻¹ *
            l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) +
          (↑(π⁻¹ * (l.intC (fun s ↦ (Real.sign lam : ℂ) *
              Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ) := by
    rw [prop_5_2_a_neg hF_mero hF_symm hlam hε hm hL hx₀ hF_bdd hFw_bdd hx hfin hsimple hsimple_circ]
    ring
  rw [hLHS]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add
    (prop_5_2_b hF_mero hF_symm hlam.ne hε hx₀ hF_bdd hx hfin hsimple hsimple_circ)
    (prop_5_2_c hlam.ne)) ?_
  apply le_of_eq
  ring

end Proposition52Neg

end CH2
