/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section6Zeros

/-!
# Section 6: Lipschitz bounds on the odd weight

`shiftError` carries the contour integral of `Φ⋆(sgn λ · z(s)) F(s) x^s`, which `coronidis` bounds
once `Φ(s) = T Φ⋆(sgn λ · z(s))` satisfies `‖Φ(s)‖ ≤ K ‖s - 1‖`. Since
`T Φ⋆(sgn λ · z(s)) = T (B(W) - B(ν))/(2πi)` with `W - ν = (2π/T)(s - 1)`, that is a Lipschitz bound
on `B(W) = (W/2)(coth(W/2) + ε)`, whose derivative is `h'(W/2)/2 + ε/2` with `h(u) = u coth u`.

* On the real axis `|h'| ≤ 1`, so `B` is `1`-Lipschitz (`norm_B_sub_le_real`): exactly the constant
  `coronidis` needs on the segment `[-1, 1]`, where the leading `γ x/log² x` comes from.
* On the strip `|Im W| ≤ π/2`, `|h'| ≤ 2.65`, so `B` is `1.9`-Lipschitz (`norm_B_sub_le_strip`).
  This replaces the paper's `|h'| < 1` on `|Im u| ≤ π/4` (first half of `lem:cothder`), which is not
  ported; the far legs of the contour have the slack to absorb it.
-/

open Complex Filter Topology

namespace CH2Section6

/-- `h(w) = w coth w`. -/
noncomputable def hcoth (w : ℂ) : ℂ := w * Complex.cosh w / Complex.sinh w

theorem hasDerivAt_hcoth {z : ℂ} (hs : Complex.sinh z ≠ 0) :
    HasDerivAt hcoth (Complex.cosh z / Complex.sinh z - z / Complex.sinh z ^ 2) z := by
  have h := (((hasDerivAt_id z).mul (Complex.hasDerivAt_cosh z)).div
    (Complex.hasDerivAt_sinh z) hs)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, id, one_mul]
  have := Complex.cosh_sq z
  field_simp
  linear_combination (-z) * this

/-- `‖sinh(a + bi)‖² = sinh² a + sin² b`. -/
theorem sq_norm_sinh (z : ℂ) :
    ‖Complex.sinh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.sin z.im ^ 2 := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  have e : Complex.sinh z = ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ)
      + ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * I := by
    conv_lhs => rw [hz]
    rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    push_cast
    ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have := Real.cosh_sq z.re
  have := Real.sin_sq_add_cos_sq z.im
  nlinarith

/-- `‖cosh(a + bi)‖ ≤ cosh a`. -/
theorem norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  have e : Complex.cosh z = ((Real.cosh z.re * Real.cos z.im : ℝ) : ℂ)
      + ((Real.sinh z.re * Real.sin z.im : ℝ) : ℂ) * I := by
    conv_lhs => rw [hz]
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    push_cast
    ring
  have hsq : ‖Complex.cosh z‖ ^ 2 ≤ Real.cosh z.re ^ 2 := by
    rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
    have := Real.cosh_sq z.re
    have := Real.sin_sq_add_cos_sq z.im
    nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im)]
  by_contra hc
  push Not at hc
  nlinarith [Real.cosh_pos z.re]

/-- `sinh` has no zeros in `0 < |z| `, `|Im z| ≤ π/4`. -/
theorem sinh_ne_zero_strip {z : ℂ} (hz : z ≠ 0) (him : |z.im| ≤ Real.pi / 4) :
    Complex.sinh z ≠ 0 := by
  intro h
  have hsq := sq_norm_sinh z
  rw [h, norm_zero] at hsq
  have h1 : Real.sinh z.re = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im)]
  have h2 : Real.sin z.im = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im)]
  have hre : z.re = 0 := Real.sinh_eq_zero.mp h1
  have hπ := Real.pi_gt_three
  have him' : z.im = 0 := by
    rcases Real.sin_eq_zero_iff.mp h2 with ⟨n, hn⟩
    have habs : |(n : ℝ) * Real.pi| ≤ Real.pi / 4 := by rw [hn]; exact him
    rw [abs_mul, abs_of_pos Real.pi_pos] at habs
    have hn0 : n = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
      nlinarith
    rw [← hn, hn0]; simp
  exact hz (Complex.ext hre him')

/-- `|h'(u)| ≤ 2.7` on `|Im u| ≤ π/4`, `u ≠ 0`. -/
theorem norm_deriv_hcoth_strip {z : ℂ} (hz : z ≠ 0) (him : |z.im| ≤ Real.pi / 4) :
    ‖Complex.cosh z / Complex.sinh z - z / Complex.sinh z ^ 2‖ ≤ 2.7 := by
  have hs := sinh_ne_zero_strip hz him
  have hπ4 : Real.pi / 4 ≤ 0.79 := by have := Real.pi_lt_d2; linarith
  have hnz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  rcases le_or_gt |z.re| 1.2 with ha | ha
  · -- near the imaginary axis: `|h'(u)| ≤ |u|`
    have h := CH2Section7.norm_deriv_mul_coth_le hz (by linarith [Real.pi_pos])
    rw [show (fun w : ℂ ↦ w * Complex.cosh w / Complex.sinh w) = hcoth from rfl,
      (hasDerivAt_hcoth hs).deriv] at h
    linarith
  · -- away from it: `|coth u| ≤ coth |a|` and `|u|/|sinh u|² ≤ (|a| + π/4)/a²`
    set a := |z.re| with ha_def
    have ha0 : 0 < a := by linarith
    have hsh : Real.sinh a ^ 2 ≤ ‖Complex.sinh z‖ ^ 2 := by
      rw [sq_norm_sinh, ha_def, ← Real.abs_sinh, sq_abs]
      nlinarith [sq_nonneg (Real.sin z.im)]
    have hsa : a ≤ Real.sinh a := Real.self_le_sinh_iff.mpr ha0.le
    have hsa0 : 0 < Real.sinh a := by linarith
    have hnsh : Real.sinh a ≤ ‖Complex.sinh z‖ := by
      nlinarith [norm_nonneg (Complex.sinh z)]
    have hcosh : ‖Complex.cosh z‖ ≤ Real.cosh a := by
      rw [ha_def, Real.cosh_abs]; exact norm_cosh_le z
    -- the `coth` term
    have hcoth : ‖Complex.cosh z / Complex.sinh z‖ ≤ 1.27 := by
      rw [norm_div]
      have h1 : ‖Complex.cosh z‖ / ‖Complex.sinh z‖ ≤ Real.cosh a / Real.sinh a := by
        rw [div_le_div_iff₀ (by linarith) hsa0]
        nlinarith [Real.cosh_pos a, norm_nonneg (Complex.cosh z)]
      rw [CH2Section7.coth_eq_one_add_two_div ha0] at h1
      have he : (8.5 : ℝ) ≤ Real.exp (2 * a) := by
        have h12 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.2)
        have hmono : Real.exp (2 * 1.2) ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by linarith)
        have : Real.exp (2 * 1.2) = Real.exp 1.2 * Real.exp 1.2 := by
          rw [← Real.exp_add]; norm_num
        nlinarith
      have h2 : 2 / (Real.exp (2 * a) - 1) ≤ 0.27 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    -- the `u/sinh² u` term
    have hsec : ‖z / Complex.sinh z ^ 2‖ ≤ 1.39 := by
      rw [norm_div, norm_pow]
      have hden : a ^ 2 ≤ ‖Complex.sinh z‖ ^ 2 := by nlinarith
      have ha2 : 0 < a ^ 2 := by positivity
      calc ‖z‖ / ‖Complex.sinh z‖ ^ 2 ≤ (a + 0.79) / a ^ 2 := by
            apply div_le_div₀ (by linarith) (by linarith) ha2 hden
        _ ≤ 1.39 := by
            rw [div_le_iff₀ ha2]; nlinarith
    calc _ ≤ ‖Complex.cosh z / Complex.sinh z‖ + ‖z / Complex.sinh z ^ 2‖ := norm_sub_le _ _
      _ ≤ 2.7 := by linarith

/-- On the real axis, `|h'(u)| ≤ 1`. -/
theorem abs_deriv_hcoth_real {u : ℝ} (hu : u ≠ 0) :
    |Real.cosh u / Real.sinh u - u / Real.sinh u ^ 2| ≤ 1 := by
  have key : ∀ v : ℝ, 0 < v → 0 ≤ Real.cosh v / Real.sinh v - v / Real.sinh v ^ 2 ∧
      Real.cosh v / Real.sinh v - v / Real.sinh v ^ 2 ≤ 1 := by
    intro v hv
    have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
    have hs2 : 0 < Real.sinh v ^ 2 := by positivity
    have e : Real.cosh v / Real.sinh v - v / Real.sinh v ^ 2
        = (Real.sinh v * Real.cosh v - v) / Real.sinh v ^ 2 := by field_simp
    rw [e]
    constructor
    · apply div_nonneg _ hs2.le
      have h2 := Real.self_le_sinh_iff.mpr (by linarith : (0 : ℝ) ≤ 2 * v)
      rw [Real.sinh_two_mul] at h2
      linarith
    · rw [div_le_one hs2]
      have hexp := Real.add_one_le_exp (-2 * v)
      have hsinh : Real.sinh v = (Real.exp v - Real.exp (-v)) / 2 := Real.sinh_eq v
      have hcosh : Real.cosh v = (Real.exp v + Real.exp (-v)) / 2 := Real.cosh_eq v
      have hm : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
      have hm2 : Real.exp (-2 * v) = Real.exp (-v) * Real.exp (-v) := by
        rw [← Real.exp_add]; ring_nf
      rw [hsinh, hcosh]
      nlinarith [Real.exp_pos v, Real.exp_pos (-v)]
  rcases lt_or_gt_of_ne hu with h | h
  · obtain ⟨h1, h2⟩ := key (-u) (by linarith)
    rw [Real.cosh_neg, Real.sinh_neg] at h1 h2
    have e : Real.cosh u / Real.sinh u - u / Real.sinh u ^ 2
        = -(Real.cosh u / -Real.sinh u - -u / (-Real.sinh u) ^ 2) := by
      rw [neg_sq]; field_simp; ring
    rw [e, abs_neg, abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := key u h
    rw [abs_le]; constructor <;> linarith

/-! ### The derivative of `B` and the two Lipschitz bounds -/

theorem hasDerivAt_B (ε : ℝ) {W : ℂ} (hW : W ≠ 0) (hs : Complex.sinh (W / 2) ≠ 0) :
    HasDerivAt (CH2.B ε)
      ((Complex.cosh (W / 2) / Complex.sinh (W / 2) - (W / 2) / Complex.sinh (W / 2) ^ 2) / 2
        + ε / 2) W := by
  have h1 : HasDerivAt (fun V : ℂ ↦ V / 2) (1 / 2) W := by
    simpa using (hasDerivAt_id W).div_const 2
  have h2 := ((hasDerivAt_hcoth hs).comp W h1).add ((h1).const_mul (ε : ℂ))
  have heq : (fun V ↦ hcoth (V / 2) + (ε : ℂ) * (V / 2)) =ᶠ[𝓝 W] CH2.B ε := by
    filter_upwards [isOpen_ne.mem_nhds hW] with V hV
    rw [CH2.B, if_neg hV, hcoth, coth_eq_cosh_div_sinh]
    ring
  refine (h2.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  ring

theorem not_pole_of_strip {W : ℂ} (hW : |W.im| ≤ Real.pi / 2) :
    ∀ n : ℤ, n ≠ 0 → W ≠ 2 * Real.pi * I * n := by
  intro n hn h
  have him := congrArg Complex.im h
  simp at him
  rw [him, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_of_pos Real.pi_pos] at hW
  have : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  nlinarith [Real.pi_pos]

theorem norm_deriv_B_zero {ε : ℝ} (hε : |ε| ≤ 1) : ‖deriv (CH2.B ε) 0‖ ≤ 1 := by
  have hA : AnalyticAt ℂ (CH2.B ε) 0 :=
    CH2.analyticAt_B ε 0 (not_pole_of_strip (by simp; positivity))
  have hc : Tendsto (fun V ↦ ‖deriv (CH2.B ε) V‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖deriv (CH2.B ε) 0‖) :=
    (hA.deriv.continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hc ?_
  have hball : ∀ᶠ V in 𝓝[≠] (0 : ℂ), ‖V‖ < 1 :=
    nhdsWithin_le_nhds (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with V hV
      simpa using hV)
  filter_upwards [hball, self_mem_nhdsWithin] with V hV hV0
  have hV0' : V ≠ 0 := hV0
  have hu0 : V / 2 ≠ 0 := div_ne_zero hV0' two_ne_zero
  have hπ := Real.pi_gt_three
  have him : |(V / 2).im| ≤ Real.pi / 4 := by
    have := Complex.abs_im_le_norm (V / 2)
    rw [norm_div, Complex.norm_ofNat] at this
    linarith
  have hs := sinh_ne_zero_strip hu0 him
  rw [(hasDerivAt_B ε hV0' hs).deriv]
  have hd := CH2Section7.norm_deriv_mul_coth_le hu0 (by linarith)
  rw [show (fun w : ℂ ↦ w * Complex.cosh w / Complex.sinh w) = hcoth from rfl,
    (hasDerivAt_hcoth hs).deriv, norm_div, Complex.norm_ofNat] at hd
  calc _ ≤ ‖(Complex.cosh (V / 2) / Complex.sinh (V / 2) - V / 2 / Complex.sinh (V / 2) ^ 2) / 2‖
        + ‖(ε : ℂ) / 2‖ := norm_add_le _ _
    _ ≤ (‖V‖ / 2) / 2 + 1 / 2 := by
        rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        gcongr
    _ ≤ 1 := by linarith

theorem differentiableAt_B_strip (ε : ℝ) {W : ℂ} (hW : |W.im| ≤ Real.pi / 2) :
    DifferentiableAt ℂ (CH2.B ε) W :=
  (CH2.analyticAt_B ε W (not_pole_of_strip hW)).differentiableAt

theorem norm_deriv_B_strip {ε : ℝ} (hε : |ε| ≤ 1) {W : ℂ} (hW : |W.im| ≤ Real.pi / 2) :
    ‖deriv (CH2.B ε) W‖ ≤ 1.85 := by
  rcases eq_or_ne W 0 with rfl | hW0
  · linarith [norm_deriv_B_zero hε]
  have hu0 : W / 2 ≠ 0 := div_ne_zero hW0 two_ne_zero
  have him : |(W / 2).im| ≤ Real.pi / 4 := by
    rw [Complex.div_ofNat_im, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have hs := sinh_ne_zero_strip hu0 him
  rw [(hasDerivAt_B ε hW0 hs).deriv]
  have hb := norm_deriv_hcoth_strip hu0 him
  calc _ ≤ ‖(Complex.cosh (W / 2) / Complex.sinh (W / 2) - W / 2 / Complex.sinh (W / 2) ^ 2) / 2‖
        + ‖(ε : ℂ) / 2‖ := norm_add_le _ _
    _ ≤ 2.7 / 2 + 1 / 2 := by
        rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        gcongr
    _ = 1.85 := by norm_num

theorem norm_deriv_B_real {ε : ℝ} (hε : |ε| ≤ 1) (r : ℝ) :
    ‖deriv (CH2.B ε) (r : ℂ)‖ ≤ 1 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simpa using norm_deriv_B_zero hε
  have hW0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
  have hu0 : (r : ℂ) / 2 ≠ 0 := div_ne_zero hW0 two_ne_zero
  have hs := sinh_ne_zero_strip hu0 (by simp; positivity)
  rw [(hasDerivAt_B ε hW0 hs).deriv]
  have hr2 : (r / 2 : ℝ) ≠ 0 := by positivity
  have hb := abs_deriv_hcoth_real hr2
  have e : Complex.cosh ((r : ℂ) / 2) / Complex.sinh ((r : ℂ) / 2)
      - (r : ℂ) / 2 / Complex.sinh ((r : ℂ) / 2) ^ 2
      = ((Real.cosh (r / 2) / Real.sinh (r / 2) - (r / 2) / Real.sinh (r / 2) ^ 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e]
  calc _ ≤ ‖((Real.cosh (r / 2) / Real.sinh (r / 2) - (r / 2) / Real.sinh (r / 2) ^ 2 : ℝ) : ℂ) / 2‖
        + ‖(ε : ℂ) / 2‖ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 / 2 := by
        rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
    _ = 1 := by norm_num

/-- **`B` is `1.85`-Lipschitz on the strip `|Im W| ≤ π/2`.** -/
theorem norm_B_sub_le_strip {ε : ℝ} (hε : |ε| ≤ 1) {W W' : ℂ} (hW : |W.im| ≤ Real.pi / 2)
    (hW' : |W'.im| ≤ Real.pi / 2) :
    ‖CH2.B ε W - CH2.B ε W'‖ ≤ 1.85 * ‖W - W'‖ := by
  set S : Set ℂ := Complex.im ⁻¹' Set.Icc (-(Real.pi / 2)) (Real.pi / 2) with hS
  have hSc : Convex ℝ S := (convex_Icc _ _).is_linear_preimage Complex.imLm.isLinear
  have mem : ∀ V : ℂ, |V.im| ≤ Real.pi / 2 → V ∈ S := fun V h ↦ abs_le.mp h
  have memS : ∀ V ∈ S, |V.im| ≤ Real.pi / 2 := fun V h ↦ abs_le.mpr h
  exact hSc.norm_image_sub_le_of_norm_deriv_le
    (fun V hV ↦ differentiableAt_B_strip ε (memS V hV))
    (fun V hV ↦ norm_deriv_B_strip hε (memS V hV)) (mem W' hW') (mem W hW)

/-- **`B` is `1`-Lipschitz on the real axis.** -/
theorem norm_B_sub_le_real {ε : ℝ} (hε : |ε| ≤ 1) (r r' : ℝ) :
    ‖CH2.B ε r - CH2.B ε r'‖ ≤ ‖(r : ℂ) - r'‖ := by
  set S : Set ℂ := Complex.im ⁻¹' {0} with hS
  have hSc : Convex ℝ S := (convex_singleton _).is_linear_preimage Complex.imLm.isLinear
  have memS : ∀ V ∈ S, V = ((V.re : ℝ) : ℂ) := fun V h ↦ Complex.ext (by simp) (by simpa using (Set.mem_singleton_iff.mp h))
  have h := hSc.norm_image_sub_le_of_norm_deriv_le (f := CH2.B ε) (C := 1)
    (fun V hV ↦ differentiableAt_B_strip ε (by rw [show V.im = 0 from hV]; simp; positivity))
    (fun V hV ↦ by rw [memS V hV]; exact norm_deriv_B_real hε _)
    (show ((r' : ℝ) : ℂ) ∈ S by simp [hS]) (show ((r : ℝ) : ℂ) ∈ S by simp [hS])
  simpa using h

end CH2Section6
