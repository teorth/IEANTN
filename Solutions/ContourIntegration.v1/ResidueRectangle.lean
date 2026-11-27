/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The residue theorem on a rectangle

For `f` holomorphic on a closed rectangle except at finitely many interior points `P`, the
integral of `f` over the boundary of the rectangle equals the sum of the integrals of `f` over
small circles about the points of `P` (`residue_theorem_rectangle`). This is the statement of
`IEANTN`'s node `ContourIntegration.v1` (`residue_theorem_rectangle`), copied verbatim: circles of
a common radius `r`, with the closed discs disjoint and strictly inside the rectangle, and the
boundary integral written as in Mathlib's `integral_boundary_rect_eq_zero_of_differentiableOn`.
No assumption is made on the nature of the singularities.

This file imports only Mathlib.

## Proof

* **A square and its inscribed circle** (`bdry_square_eq_circleIntegral`): if `f` is holomorphic
  on the punctured disc of radius `e² s` about `ρ`, the boundary integral of the square of
  half-side `s` about `ρ` equals `∮_{|z - ρ| = s} f`. In the coordinate `u = log (z - ρ)`,
  `h(u) = f(ρ + e^u) e^u` is holomorphic on a ball `B` of the half-plane `Re u < log s + 2` and
  `2πi`-periodic; it has a primitive `H` on `B` (Mathlib's `DifferentiableOn.isExactOn_ball`), and
  `H(u + 2πi) - H(u)` is constant. Both integrals are values of this constant: the circle integral
  by the fundamental theorem of calculus along `u = log s + iθ`, and the square's by the
  fundamental theorem of calculus along each side, using `H ∘ L` with a branch `L` of
  `log (z - ρ)` adapted to the side (`log`, `log + 2πi`, `log (-·) + πi`).
* **Pulling a rectangle to a small square** (`bdry_eq_bdry_square`): cutting along the four lines
  through `ρ.re ± s`, `ρ.im ± s`, the eight outer pieces contribute nothing (Cauchy's theorem on a
  rectangle).
* **Induction on `P`** (`bdry_eq_sum_of_separated`): after shrinking the circles
  (Mathlib's `circleIntegral_eq_of_differentiable_on_annulus_off_countable`) so that distinct
  real or imaginary parts of points of `P` differ by more than three radii, a vertical or
  horizontal line splits `P` into two nonempty parts and the rectangle into two rectangles.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/


open Complex Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Real Interval

noncomputable section

namespace ResidueRectangle

/-- The integral of `f` over the boundary of the rectangle with opposite corners `z` and `w`, in
the shape of `IEANTN`'s `ContourIntegration.v1` (and of Mathlib's
`integral_boundary_rect_eq_zero_of_differentiableOn`). -/
def bdry (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
    + I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-! ### The fundamental theorem of calculus along horizontal and vertical segments -/

theorem integral_horizontal {Φ g : ℂ → ℂ} {a b c : ℝ} (hab : a ≤ b)
    (hΦ : ∀ x ∈ Icc a b, HasDerivAt Φ (g (x + c * I)) (x + c * I))
    (hg : ContinuousOn (fun x : ℝ ↦ g (x + c * I)) (Icc a b)) :
    ∫ x in a..b, g (x + c * I) = Φ (b + c * I) - Φ (a + c * I) := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun x : ℝ ↦ Φ (x + c * I)) (g (x + c * I)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hin : HasDerivAt (fun x : ℝ ↦ (x : ℂ) + c * I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((c : ℂ) * I)
    have h := (hΦ x hx).comp x hin
    rw [mul_one] at h
    exact h
  exact integral_eq_sub_of_hasDerivAt hderiv
    ((hg.mono (by rw [uIcc_of_le hab])).intervalIntegrable)

theorem integral_vertical {Φ g : ℂ → ℂ} {a b c : ℝ} (hab : a ≤ b)
    (hΦ : ∀ y ∈ Icc a b, HasDerivAt Φ (g (c + y * I)) (c + y * I))
    (hg : ContinuousOn (fun y : ℝ ↦ g (c + y * I)) (Icc a b)) :
    I * ∫ y in a..b, g (c + y * I) = Φ (c + b * I) - Φ (c + a * I) := by
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun y : ℝ ↦ Φ (c + y * I)) (g (c + y * I) * I) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hin : HasDerivAt (fun y : ℝ ↦ (c : ℂ) + y * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (c : ℂ)
    exact (hΦ y hy).comp y hin
  rw [mul_comm, ← intervalIntegral.integral_mul_const]
  exact integral_eq_sub_of_hasDerivAt hderiv
    (((hg.mul continuousOn_const).mono (by rw [uIcc_of_le hab])).intervalIntegrable)

/-! ### A square and its inscribed circle -/

section Square

variable {f H : ℂ → ℂ} {ρ : ℂ}

/-- The chain rule for `H (L (z - ρ))`, where `H' (u) = f(ρ + e^u) e^u` and `L` is a branch of the
logarithm. -/
theorem hasDerivAt_comp_log {L : ℂ → ℂ} {z : ℂ} (hz : z ≠ ρ)
    (hL : HasDerivAt L (z - ρ)⁻¹ (z - ρ)) (hexp : Complex.exp (L (z - ρ)) = z - ρ)
    (hH : HasDerivAt H (f (ρ + Complex.exp (L (z - ρ))) * Complex.exp (L (z - ρ))) (L (z - ρ))) :
    HasDerivAt (fun z ↦ H (L (z - ρ))) (f z) z := by
  have h1 : HasDerivAt (fun z : ℂ ↦ z - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  have h2 := hH.comp z (hL.comp z h1)
  have hz' : z - ρ ≠ 0 := sub_ne_zero.2 hz
  convert! h2 using 1
  rw [hexp, add_sub_cancel]
  field_simp

/-- The ball of the `u`-plane, `u = log (z - ρ)`, on which the primitive lives. -/
def uCenter (s : ℝ) : ℂ := ((Real.log s - 7 : ℝ) : ℂ) + ((3 * π / 4 : ℝ) : ℂ) * I

theorem mem_ball_uCenter {s : ℝ} {u : ℂ} (h1 : Real.log s ≤ u.re)
    (h2 : u.re ≤ Real.log s + Real.log 2) (h3 : -(π / 2) ≤ u.im) (h4 : u.im ≤ 2 * π) :
    u ∈ ball (uCenter s) 9 := by
  rw [mem_ball, Complex.dist_eq, ← sq_lt_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm,
    Complex.normSq_apply]
  have hre : (u - uCenter s).re = u.re - (Real.log s - 7) := by simp [uCenter]
  have him : (u - uCenter s).im = u.im - 3 * π / 4 := by simp [uCenter]
  rw [hre, him]
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have e1 : (u.re - (Real.log s - 7)) * (u.re - (Real.log s - 7)) ≤ 8 * 8 := by
    have : 0 ≤ u.re - (Real.log s - 7) := by linarith
    have : u.re - (Real.log s - 7) ≤ 8 := by linarith
    nlinarith
  have e2 : (u.im - 3 * π / 4) * (u.im - 3 * π / 4) ≤ (5 * π / 4) * (5 * π / 4) := by
    have : -(5 * π / 4) ≤ u.im - 3 * π / 4 := by linarith
    have : u.im - 3 * π / 4 ≤ 5 * π / 4 := by linarith
    nlinarith
  have e3 : (5 * π / 4) * (5 * π / 4) < 15.51 := by nlinarith
  norm_num at e1 ⊢
  linarith

theorem re_lt_of_mem_ball_uCenter {s : ℝ} {u : ℂ} (hu : u ∈ ball (uCenter s) 9) :
    u.re < Real.log s + 2 := by
  rw [mem_ball, Complex.dist_eq] at hu
  have h := (Complex.abs_re_le_norm (u - uCenter s)).trans_lt hu
  have hre : (u - uCenter s).re = u.re - (Real.log s - 7) := by simp [uCenter]
  rw [hre] at h
  linarith [(abs_lt.1 h).2]

theorem norm_bounds_of_side {w : ℂ} {s : ℝ} (h1 : |w.re| ≤ s) (h2 : |w.im| ≤ s)
    (h3 : |w.re| = s ∨ |w.im| = s) : s ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * s := by
  refine ⟨?_, (Complex.norm_le_abs_re_add_abs_im w).trans (by linarith)⟩
  rcases h3 with h | h
  · rw [← h]; exact Complex.abs_re_le_norm w
  · rw [← h]; exact Complex.abs_im_le_norm w

theorem log_neg_add_pi_of_im_pos {x : ℂ} (hx : 0 < x.im) :
    Complex.log (-x) + π * I = Complex.log x := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]

theorem log_neg_add_pi_of_im_neg {x : ℂ} (hx : x.im < 0) :
    Complex.log (-x) + π * I = Complex.log x + 2 * π * I := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im,
    Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]
  ring

/-- **A square and its inscribed circle**: if `f` is holomorphic on the punctured disc of radius
`e² s` about `ρ`, then the boundary integral of the square of half-side `s` about `ρ` is
`∮_{|z - ρ| = s} f`. -/
theorem bdry_square_eq_circleIntegral {s : ℝ} (hs : 0 < s)
    (hf : ∀ z : ℂ, z ≠ ρ → ‖z - ρ‖ < s * Real.exp 2 → DifferentiableAt ℂ f z) :
    bdry f (ρ - s - s * I) (ρ + s + s * I) = ∮ z in C(ρ, s), f z := by
  set B := ball (uCenter s) 9 with hB
  set h : ℂ → ℂ := fun u ↦ f (ρ + Complex.exp u) * Complex.exp u with hh
  have hfB : ∀ u ∈ B, DifferentiableAt ℂ f (ρ + Complex.exp u) := by
    intro u hu
    refine hf _ (by simp [Complex.exp_ne_zero]) ?_
    rw [add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp u.re < Real.exp (Real.log s + 2) :=
          Real.exp_lt_exp.2 (re_lt_of_mem_ball_uCenter hu)
      _ = s * Real.exp 2 := by rw [Real.exp_add, Real.exp_log hs]
  have hhB : DifferentiableOn ℂ h B := fun u hu ↦
    (((hfB u hu).comp u ((differentiableAt_const ρ).add (differentiableAt_exp))).mul
      differentiableAt_exp).differentiableWithinAt
  obtain ⟨H, hH⟩ := hhB.isExactOn_ball
  -- `H (u + 2πi) - H u` is constant
  set D : ℂ → ℂ := fun u ↦ H (u + 2 * π * I) - H u with hD
  set V := B ∩ ball (uCenter s - 2 * π * I) 9 with hV
  have hdist : ∀ u : ℂ, dist (u + 2 * π * I) (uCenter s) = dist u (uCenter s - 2 * π * I) :=
    fun u ↦ by rw [Complex.dist_eq, Complex.dist_eq]; congr 1; ring
  have hshift : ∀ u ∈ V, u + 2 * π * I ∈ B := by
    intro u hu
    have := hu.2
    rw [mem_ball] at this ⊢
    rwa [hdist]
  have hDderiv : ∀ u ∈ V, HasDerivAt D 0 u := by
    intro u hu
    have h1 := (hH _ (hshift u hu)).comp u ((hasDerivAt_id u).add_const (2 * π * I))
    have h2 := h1.sub (hH u hu.1)
    convert! h2 using 1
    simp only [hh, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I]
    ring_nf
  have hDconst : ∀ u ∈ V, ∀ v ∈ V, D u = D v := fun u hu v hv ↦
    (isOpen_ball.inter isOpen_ball).is_const_of_deriv_eq_zero
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
      (fun x hx ↦ (hDderiv x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hDderiv x hx).deriv) hu hv
  have hmemV : ∀ u : ℂ, Real.log s ≤ u.re → u.re ≤ Real.log s + Real.log 2 → -(π / 2) ≤ u.im →
      u.im + 2 * π ≤ 2 * π → u ∈ V := by
    intro u h1 h2 h3 h4
    refine ⟨mem_ball_uCenter h1 h2 h3 (by linarith [Real.pi_pos]), ?_⟩
    have := mem_ball_uCenter (u := u + 2 * π * I) (s := s) (by simpa using h1) (by simpa using h2)
      (by simp; linarith [Real.pi_pos]) (by simpa using h4)
    rw [mem_ball] at this ⊢
    rwa [hdist] at this
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  -- the circle
  have hcirc : (∮ z in C(ρ, s), f z) = D (Real.log s) := by
    have hpath : ∀ θ : ℝ, Complex.exp ((Real.log s : ℂ) + θ * I) = s * Complex.exp (θ * I) := by
      intro θ
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hs]
    have hint : ∀ θ : ℝ, deriv (circleMap ρ s) θ • f (circleMap ρ s θ) =
        h ((Real.log s : ℂ) + θ * I) * I := by
      intro θ
      rw [deriv_circleMap, smul_eq_mul, circleMap, circleMap]
      simp only [hh, hpath]
      ring
    have hmemθ : ∀ θ ∈ Icc (0 : ℝ) (2 * π), (Real.log s : ℂ) + θ * I ∈ B := fun θ hθ ↦
      mem_ball_uCenter (by simp) (by simp [hl2]) (by simp; linarith [hθ.1, Real.pi_pos])
        (by simpa using hθ.2)
    have hderiv : ∀ θ ∈ uIcc 0 (2 * π), HasDerivAt (fun θ : ℝ ↦ H ((Real.log s : ℂ) + θ * I))
        (h ((Real.log s : ℂ) + θ * I) * I) θ := by
      intro θ hθ
      rw [uIcc_of_le (by positivity)] at hθ
      have hin : HasDerivAt (fun θ : ℝ ↦ (Real.log s : ℂ) + θ * I) I θ := by
        simpa using (((hasDerivAt_id θ).ofReal_comp).mul_const I).const_add ((Real.log s : ℂ))
      exact (hH _ (hmemθ θ hθ)).comp θ hin
    have hcont : ContinuousOn (fun θ : ℝ ↦ h ((Real.log s : ℂ) + θ * I) * I) (uIcc 0 (2 * π)) := by
      rw [uIcc_of_le (by positivity)]
      exact (hhB.continuousOn.comp (by fun_prop : Continuous fun θ : ℝ ↦
        (Real.log s : ℂ) + θ * I).continuousOn hmemθ).mul continuousOn_const
    rw [circleIntegral]
    simp_rw [hint]
    rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    simp [hD]
  -- the square
  set a := ρ.re with ha
  set b := ρ.im with hb
  have hρ : ρ = (a : ℂ) + b * I := (Complex.re_add_im ρ).symm
  have hes : 2 * s < s * Real.exp 2 := by
    have := Real.add_one_le_exp 2
    nlinarith
  have hfside : ∀ z : ℂ, |(z - ρ).re| ≤ s → |(z - ρ).im| ≤ s →
      (|(z - ρ).re| = s ∨ |(z - ρ).im| = s) → DifferentiableAt ℂ f z := by
    intro z h1 h2 h3
    have hn := norm_bounds_of_side h1 h2 h3
    refine hf z (fun hz ↦ ?_) (by linarith [hn.2])
    rw [hz, sub_self, norm_zero] at hn
    linarith [hn.1]
  have hmemL : ∀ (w u : ℂ), |w.re| ≤ s → |w.im| ≤ s → (|w.re| = s ∨ |w.im| = s) →
      u.re = Real.log ‖w‖ → -(π / 2) ≤ u.im → u.im ≤ 2 * π → u ∈ B := by
    intro w u h1 h2 h3 hre him1 him2
    have hn := norm_bounds_of_side h1 h2 h3
    refine mem_ball_uCenter ?_ ?_ him1 him2
    · rw [hre]; exact Real.log_le_log hs hn.1
    · rw [hre, ← Real.log_mul hs.ne' two_ne_zero]
      exact Real.log_le_log (by linarith [hn.1]) (by linarith [hn.2])
  set Φ₁ : ℂ → ℂ := fun z ↦ H (Complex.log (z - ρ)) with hΦ₁
  set Φ₂ : ℂ → ℂ := fun z ↦ H (Complex.log (z - ρ) + 2 * π * I) with hΦ₂
  set Φ₃ : ℂ → ℂ := fun z ↦ H (Complex.log (-(z - ρ)) + π * I) with hΦ₃
  have hcontH : ∀ c : ℝ, ∀ z : ℝ → ℂ, Continuous z → (∀ t ∈ Icc (a - s) (a + s),
      DifferentiableAt ℂ f (z t)) → ContinuousOn (fun t ↦ f (z t)) (Icc (a - s) (a + s)) :=
    fun _ z hz hd t ht ↦ ((hd t ht).continuousAt.comp hz.continuousAt).continuousWithinAt
  have hcontV : ∀ z : ℝ → ℂ, Continuous z → (∀ t ∈ Icc (b - s) (b + s),
      DifferentiableAt ℂ f (z t)) → ContinuousOn (fun t ↦ f (z t)) (Icc (b - s) (b + s)) :=
    fun z hz hd t ht ↦ ((hd t ht).continuousAt.comp hz.continuousAt).continuousWithinAt
  -- bottom side: the branch `log + 2πi`
  have hbot : ∫ x in (a - s)..(a + s), f (x + ((b - s : ℝ) : ℂ) * I) =
      Φ₂ ((a + s : ℝ) + ((b - s : ℝ) : ℂ) * I) - Φ₂ ((a - s : ℝ) + ((b - s : ℝ) : ℂ) * I) := by
    have key : ∀ x ∈ Icc (a - s) (a + s), DifferentiableAt ℂ f (x + ((b - s : ℝ) : ℂ) * I) ∧
        HasDerivAt Φ₂ (f (x + ((b - s : ℝ) : ℂ) * I)) (x + ((b - s : ℝ) : ℂ) * I) := by
      intro x hx
      have hw : (x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ = ((x - a : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I := by
        rw [hρ]; push_cast; ring
      have hwre : ((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ).re = x - a := by rw [hw]; simp
      have hwim : ((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ).im = -s := by rw [hw]; simp
      have h1 : |((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ).re| ≤ s := by
        rw [hwre, abs_le]; constructor <;> linarith [hx.1, hx.2]
      have h2 : |((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ).im| ≤ s := by
        rw [hwim, abs_neg, abs_of_pos hs]
      have h3 : |((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ).im| = s := by
        rw [hwim, abs_neg, abs_of_pos hs]
      have hneg : ((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ).im < 0 := by rw [hwim]; linarith
      have hslit : (x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ ∈ slitPlane :=
        Complex.mem_slitPlane_iff.2 (Or.inr hneg.ne)
      have hz0 := slitPlane_ne_zero hslit
      refine ⟨hfside _ h1 h2 (Or.inr h3), ?_⟩
      have hlow := Complex.neg_pi_lt_arg ((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ)
      have hup := Complex.arg_neg_iff.2 hneg
      have him : (Complex.log ((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ) + 2 * π * I).im =
          Complex.arg ((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ) + 2 * π := by simp [Complex.log_im]
      have hmem := hmemL _ (Complex.log ((x : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ) + 2 * π * I) h1 h2
        (Or.inr h3) (by simp [Complex.log_re])
        (by rw [him]; linarith [Real.pi_pos])
        (by rw [him]; linarith)
      exact hasDerivAt_comp_log (L := fun w ↦ Complex.log w + 2 * π * I) (sub_ne_zero.1 hz0)
        ((Complex.hasDerivAt_log hslit).add_const _)
        (by rw [Complex.exp_add, Complex.exp_log hz0, Complex.exp_two_pi_mul_I,
          mul_one]) (hH _ hmem)
    exact integral_horizontal (by linarith) (fun x hx ↦ (key x hx).2)
      (hcontH (b - s) _ (by fun_prop) fun x hx ↦ (key x hx).1)
  -- top side: the principal branch
  have htop : ∫ x in (a - s)..(a + s), f (x + ((b + s : ℝ) : ℂ) * I) =
      Φ₁ ((a + s : ℝ) + ((b + s : ℝ) : ℂ) * I) - Φ₁ ((a - s : ℝ) + ((b + s : ℝ) : ℂ) * I) := by
    have key : ∀ x ∈ Icc (a - s) (a + s), DifferentiableAt ℂ f (x + ((b + s : ℝ) : ℂ) * I) ∧
        HasDerivAt Φ₁ (f (x + ((b + s : ℝ) : ℂ) * I)) (x + ((b + s : ℝ) : ℂ) * I) := by
      intro x hx
      have hw : (x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ = ((x - a : ℝ) : ℂ) + ((s : ℝ) : ℂ) * I := by
        rw [hρ]; push_cast; ring
      have hwre : ((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ).re = x - a := by rw [hw]; simp
      have hwim : ((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ).im = s := by rw [hw]; simp
      have h1 : |((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ).re| ≤ s := by
        rw [hwre, abs_le]; constructor <;> linarith [hx.1, hx.2]
      have h3 : |((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ).im| = s := by
        rw [hwim, abs_of_pos hs]
      have hpos : 0 < ((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ).im := by rw [hwim]; exact hs
      have hslit : (x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ ∈ slitPlane :=
        Complex.mem_slitPlane_iff.2 (Or.inr hpos.ne')
      have hz0 := slitPlane_ne_zero hslit
      refine ⟨hfside _ h1 h3.le (Or.inr h3), ?_⟩
      have hlow := Complex.arg_nonneg_iff.2 hpos.le
      have hup := Complex.arg_le_pi ((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ)
      have him : (Complex.log ((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ)).im =
          Complex.arg ((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ) := Complex.log_im _
      have hmem := hmemL _ (Complex.log ((x : ℂ) + ((b + s : ℝ) : ℂ) * I - ρ)) h1 h3.le
        (Or.inr h3) (by simp [Complex.log_re])
        (by rw [him]; linarith [Real.pi_pos])
        (by rw [him]; linarith [Real.pi_pos])
      exact hasDerivAt_comp_log (L := Complex.log) (sub_ne_zero.1 hz0)
        (Complex.hasDerivAt_log hslit) (Complex.exp_log hz0) (hH _ hmem)
    exact integral_horizontal (by linarith) (fun x hx ↦ (key x hx).2)
      (hcontH (b + s) _ (by fun_prop) fun x hx ↦ (key x hx).1)
  -- right side: the principal branch
  have hright : I * ∫ y in (b - s)..(b + s), f (((a + s : ℝ) : ℂ) + y * I) =
      Φ₁ ((a + s : ℝ) + ((b + s : ℝ) : ℂ) * I) - Φ₁ ((a + s : ℝ) + ((b - s : ℝ) : ℂ) * I) := by
    have key : ∀ y ∈ Icc (b - s) (b + s), DifferentiableAt ℂ f (((a + s : ℝ) : ℂ) + y * I) ∧
        HasDerivAt Φ₁ (f (((a + s : ℝ) : ℂ) + y * I)) (((a + s : ℝ) : ℂ) + y * I) := by
      intro y hy
      have hw : ((a + s : ℝ) : ℂ) + y * I - ρ = ((s : ℝ) : ℂ) + ((y - b : ℝ) : ℂ) * I := by
        rw [hρ]; push_cast; ring
      have hwre : (((a + s : ℝ) : ℂ) + y * I - ρ).re = s := by rw [hw]; simp
      have hwim : (((a + s : ℝ) : ℂ) + y * I - ρ).im = y - b := by rw [hw]; simp
      have h1 : |(((a + s : ℝ) : ℂ) + y * I - ρ).re| = s := by rw [hwre, abs_of_pos hs]
      have h2 : |(((a + s : ℝ) : ℂ) + y * I - ρ).im| ≤ s := by
        rw [hwim, abs_le]; constructor <;> linarith [hy.1, hy.2]
      have hpos : 0 < (((a + s : ℝ) : ℂ) + y * I - ρ).re := by rw [hwre]; exact hs
      have hslit : ((a + s : ℝ) : ℂ) + y * I - ρ ∈ slitPlane :=
        Complex.mem_slitPlane_iff.2 (Or.inl hpos)
      have hz0 := slitPlane_ne_zero hslit
      refine ⟨hfside _ h1.le h2 (Or.inl h1), ?_⟩
      have harg := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hpos))
      have him : (Complex.log (((a + s : ℝ) : ℂ) + y * I - ρ)).im =
          Complex.arg (((a + s : ℝ) : ℂ) + y * I - ρ) := Complex.log_im _
      have hmem := hmemL _ (Complex.log (((a + s : ℝ) : ℂ) + y * I - ρ)) h1.le h2
        (Or.inl h1) (by simp [Complex.log_re])
        (by rw [him]; linarith [harg.1])
        (by rw [him]; linarith [harg.2, Real.pi_pos])
      exact hasDerivAt_comp_log (L := Complex.log) (sub_ne_zero.1 hz0)
        (Complex.hasDerivAt_log hslit) (Complex.exp_log hz0) (hH _ hmem)
    exact integral_vertical (by linarith) (fun y hy ↦ (key y hy).2)
      (hcontV _ (by fun_prop) fun y hy ↦ (key y hy).1)
  -- left side: the branch `log (-·) + πi`
  have hleft : I * ∫ y in (b - s)..(b + s), f (((a - s : ℝ) : ℂ) + y * I) =
      Φ₃ ((a - s : ℝ) + ((b + s : ℝ) : ℂ) * I) - Φ₃ ((a - s : ℝ) + ((b - s : ℝ) : ℂ) * I) := by
    have key : ∀ y ∈ Icc (b - s) (b + s), DifferentiableAt ℂ f (((a - s : ℝ) : ℂ) + y * I) ∧
        HasDerivAt Φ₃ (f (((a - s : ℝ) : ℂ) + y * I)) (((a - s : ℝ) : ℂ) + y * I) := by
      intro y hy
      have hw : ((a - s : ℝ) : ℂ) + y * I - ρ = ((-s : ℝ) : ℂ) + ((y - b : ℝ) : ℂ) * I := by
        rw [hρ]; push_cast; ring
      have hwre : (((a - s : ℝ) : ℂ) + y * I - ρ).re = -s := by rw [hw]; simp
      have hwim : (((a - s : ℝ) : ℂ) + y * I - ρ).im = y - b := by rw [hw]; simp
      have h1 : |(((a - s : ℝ) : ℂ) + y * I - ρ).re| = s := by rw [hwre, abs_neg, abs_of_pos hs]
      have h2 : |(((a - s : ℝ) : ℂ) + y * I - ρ).im| ≤ s := by
        rw [hwim, abs_le]; constructor <;> linarith [hy.1, hy.2]
      have hpos : 0 < (-(((a - s : ℝ) : ℂ) + y * I - ρ)).re := by
        rw [Complex.neg_re, hwre]; linarith
      have hslit : -(((a - s : ℝ) : ℂ) + y * I - ρ) ∈ slitPlane :=
        Complex.mem_slitPlane_iff.2 (Or.inl hpos)
      have hz0 : ((a - s : ℝ) : ℂ) + y * I - ρ ≠ 0 := fun h0 ↦ by
        rw [h0, neg_zero] at hslit; exact slitPlane_ne_zero hslit rfl
      refine ⟨hfside _ h1.le h2 (Or.inl h1), ?_⟩
      have harg := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hpos))
      have him : (Complex.log (-(((a - s : ℝ) : ℂ) + y * I - ρ)) + π * I).im =
          Complex.arg (-(((a - s : ℝ) : ℂ) + y * I - ρ)) + π := by simp [Complex.log_im]
      have hmem := hmemL _ (Complex.log (-(((a - s : ℝ) : ℂ) + y * I - ρ)) + π * I) h1.le h2
        (Or.inl h1) (by rw [Complex.add_re, Complex.log_re, norm_neg]; simp)
        (by rw [him]; linarith [harg.1, Real.pi_pos])
        (by rw [him]; linarith [harg.2, Real.pi_pos])
      have hL : HasDerivAt (fun w ↦ Complex.log (-w) + π * I)
          (((a - s : ℝ) : ℂ) + y * I - ρ)⁻¹ (((a - s : ℝ) : ℂ) + y * I - ρ) := by
        have hn : HasDerivAt (fun x : ℂ ↦ -x) (-1) (((a - s : ℝ) : ℂ) + y * I - ρ) := by
          exact hasDerivAt_neg _
        have := (hn.clog hslit).add_const ((π : ℂ) * I)
        convert! this using 1
        field_simp
      exact hasDerivAt_comp_log (L := fun w ↦ Complex.log (-w) + π * I) (sub_ne_zero.1 hz0) hL
        (by rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hz0),
          Complex.exp_pi_mul_I]; ring) (hH _ hmem)
    exact integral_vertical (by linarith) (fun y hy ↦ (key y hy).2)
      (hcontV _ (by fun_prop) fun y hy ↦ (key y hy).1)
  -- the corners
  have hTL :
      Φ₁ ((a - s : ℝ) + ((b + s : ℝ) : ℂ) * I) = Φ₃ ((a - s : ℝ) + ((b + s : ℝ) : ℂ) * I) := by
    simp only [hΦ₁, hΦ₃]
    rw [log_neg_add_pi_of_im_pos]
    rw [hρ]; simp; linarith
  have hBL :
      Φ₃ ((a - s : ℝ) + ((b - s : ℝ) : ℂ) * I) = Φ₂ ((a - s : ℝ) + ((b - s : ℝ) : ℂ) * I) := by
    simp only [hΦ₂, hΦ₃]
    rw [log_neg_add_pi_of_im_neg]
    rw [hρ]; simp; linarith
  have hBR : Φ₂ ((a + s : ℝ) + ((b - s : ℝ) : ℂ) * I) - Φ₁ ((a + s : ℝ) + ((b - s : ℝ) : ℂ) * I) =
      D (Complex.log ((s : ℂ) - s * I)) := by
    have hw : ((a + s : ℝ) : ℂ) + ((b - s : ℝ) : ℂ) * I - ρ = (s : ℂ) - s * I := by
      rw [hρ]; push_cast; ring
    simp only [hΦ₁, hΦ₂, hD, hw]
  -- the square equals `D (log (s - si))`
  have hsq : bdry f (ρ - s - s * I) (ρ + s + s * I) = D (Complex.log ((s : ℂ) - s * I)) := by
    have hzre : (ρ - s - s * I).re = a - s := by simp [ha]
    have hzim : (ρ - s - s * I).im = b - s := by simp [hb]
    have hwre : (ρ + s + s * I).re = a + s := by simp [ha]
    have hwim : (ρ + s + s * I).im = b + s := by simp [hb]
    rw [bdry, hzre, hzim, hwre, hwim, hbot, htop, hright, hleft, ← hBR, hTL, ← hBL]
    ring
  -- conclusion
  rw [hsq, hcirc]
  refine hDconst _ ?_ _ ?_
  · have hw : (Complex.log ((s : ℂ) - s * I)).re = Real.log ‖(s : ℂ) - s * I‖ := Complex.log_re _
    have hn : s ≤ ‖(s : ℂ) - s * I‖ ∧ ‖(s : ℂ) - s * I‖ ≤ 2 * s :=
      norm_bounds_of_side (by simp [abs_of_pos hs]) (by simp [abs_of_pos hs])
        (Or.inl (by simp [abs_of_pos hs]))
    have harg := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simp [hs] :
      0 < ((s : ℂ) - s * I).re)))
    have hneg := Complex.arg_neg_iff.2 (by simp [hs] : ((s : ℂ) - s * I).im < 0)
    refine hmemV _ ?_ ?_ ?_ ?_
    · rw [hw]; exact Real.log_le_log hs hn.1
    · rw [hw, ← Real.log_mul hs.ne' two_ne_zero]
      exact Real.log_le_log (by linarith [hn.1]) (by linarith [hn.2])
    · rw [Complex.log_im]; linarith [harg.1]
    · rw [Complex.log_im]; linarith
  · refine hmemV _ (by simp) (by simp [hl2]) (by simp; linarith [Real.pi_pos]) (by simp)

end Square

/-! ### Splitting a rectangle; Cauchy's theorem -/

section Split

variable {f : ℂ → ℂ}

theorem bdry_eq_zero {z w : ℂ} (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    bdry f z w = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf
  simpa only [bdry, smul_eq_mul] using this

theorem intervalIntegrable_horizontal {K : Set ℂ} (hf : ContinuousOn f K) {a b c : ℝ}
    (h : ∀ x ∈ [[a, b]], (x : ℂ) + c * I ∈ K) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + c * I)) volume a b :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + c * I).continuousOn
    h).intervalIntegrable

theorem intervalIntegrable_vertical {K : Set ℂ} (hf : ContinuousOn f K) {a b c : ℝ}
    (h : ∀ y ∈ [[a, b]], (c : ℂ) + y * I ∈ K) :
    IntervalIntegrable (fun y : ℝ ↦ f (c + y * I)) volume a b :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (c : ℂ) + y * I).continuousOn
    h).intervalIntegrable

/-- Cutting a rectangle along the vertical line `Re z = c`. -/
theorem bdry_split_re {K : Set ℂ} (hf : ContinuousOn f K) {z w : ℂ} {c : ℝ} (hc1 : z.re ≤ c)
    (hc2 : c ≤ w.re) (hbot : ∀ x ∈ Icc z.re w.re, (x : ℂ) + z.im * I ∈ K)
    (htop : ∀ x ∈ Icc z.re w.re, (x : ℂ) + w.im * I ∈ K) :
    bdry f z w = bdry f z (c + w.im * I) + bdry f (c + z.im * I) w := by
  have hs1 : [[z.re, c]] ⊆ Icc z.re w.re := by
    rw [uIcc_of_le hc1]; exact Icc_subset_Icc le_rfl hc2
  have hs2 : [[c, w.re]] ⊆ Icc z.re w.re := by
    rw [uIcc_of_le hc2]; exact Icc_subset_Icc hc1 le_rfl
  have h1 := intervalIntegrable_horizontal hf fun x hx ↦ hbot x (hs1 hx)
  have h2 := intervalIntegrable_horizontal hf fun x hx ↦ hbot x (hs2 hx)
  have h3 := intervalIntegrable_horizontal hf fun x hx ↦ htop x (hs1 hx)
  have h4 := intervalIntegrable_horizontal hf fun x hx ↦ htop x (hs2 hx)
  have e1 : ((c : ℂ) + w.im * I).re = c := by simp
  have e2 : ((c : ℂ) + w.im * I).im = w.im := by simp
  have e3 : ((c : ℂ) + z.im * I).re = c := by simp
  have e4 : ((c : ℂ) + z.im * I).im = z.im := by simp
  simp only [bdry, e1, e2, e3, e4]
  rw [← integral_add_adjacent_intervals h1 h2, ← integral_add_adjacent_intervals h3 h4]
  ring

/-- Cutting a rectangle along the horizontal line `Im z = d`. -/
theorem bdry_split_im {K : Set ℂ} (hf : ContinuousOn f K) {z w : ℂ} {d : ℝ} (hd1 : z.im ≤ d)
    (hd2 : d ≤ w.im) (hright : ∀ y ∈ Icc z.im w.im, (w.re : ℂ) + y * I ∈ K)
    (hleft : ∀ y ∈ Icc z.im w.im, (z.re : ℂ) + y * I ∈ K) :
    bdry f z w = bdry f z (w.re + d * I) + bdry f (z.re + d * I) w := by
  have hs1 : [[z.im, d]] ⊆ Icc z.im w.im := by
    rw [uIcc_of_le hd1]; exact Icc_subset_Icc le_rfl hd2
  have hs2 : [[d, w.im]] ⊆ Icc z.im w.im := by
    rw [uIcc_of_le hd2]; exact Icc_subset_Icc hd1 le_rfl
  have h1 := intervalIntegrable_vertical hf fun y hy ↦ hright y (hs1 hy)
  have h2 := intervalIntegrable_vertical hf fun y hy ↦ hright y (hs2 hy)
  have h3 := intervalIntegrable_vertical hf fun y hy ↦ hleft y (hs1 hy)
  have h4 := intervalIntegrable_vertical hf fun y hy ↦ hleft y (hs2 hy)
  have e1 : ((w.re : ℂ) + d * I).re = w.re := by simp
  have e2 : ((w.re : ℂ) + d * I).im = d := by simp
  have e3 : ((z.re : ℂ) + d * I).re = z.re := by simp
  have e4 : ((z.re : ℂ) + d * I).im = d := by simp
  simp only [bdry, e1, e2, e3, e4]
  rw [← integral_add_adjacent_intervals h1 h2, ← integral_add_adjacent_intervals h3 h4]
  ring

end Split

/-! ### Pulling a rectangle to a small square -/

theorem mem_rect {p q u : ℂ} (hpq1 : p.re ≤ q.re) (hpq2 : p.im ≤ q.im) :
    u ∈ [[p.re, q.re]] ×ℂ [[p.im, q.im]] ↔
      (p.re ≤ u.re ∧ u.re ≤ q.re) ∧ (p.im ≤ u.im ∧ u.im ≤ q.im) := by
  rw [mem_reProdIm, uIcc_of_le hpq1, uIcc_of_le hpq2]
  rfl

/-- If `f` is holomorphic on a rectangle except at an interior point `ρ`, the boundary integral
equals that of any square about `ρ` inside the rectangle. -/
theorem bdry_eq_bdry_square {f : ℂ → ℂ} {z w ρ : ℂ} {s : ℝ} (hs : 0 < s)
    (h1 : z.re < ρ.re - s) (h2 : ρ.re + s < w.re) (h3 : z.im < ρ.im - s) (h4 : ρ.im + s < w.im)
    (hf : DifferentiableOn ℂ f (([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ {ρ})) :
    bdry f z w = bdry f (ρ - s - s * I) (ρ + s + s * I) := by
  set K := ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ {ρ} with hK
  have hc : ContinuousOn f K := hf.continuousOn
  have hzw1 : z.re ≤ w.re := by linarith
  have hzw2 : z.im ≤ w.im := by linarith
  -- a point of the rectangle different from `ρ` is in `K`
  have hmemK : ∀ u : ℂ, z.re ≤ u.re → u.re ≤ w.re → z.im ≤ u.im → u.im ≤ w.im →
      (u.re ≠ ρ.re ∨ u.im ≠ ρ.im) → u ∈ K := by
    intro u a1 a2 a3 a4 hne
    refine ⟨(mem_rect hzw1 hzw2).2 ⟨⟨a1, a2⟩, a3, a4⟩, fun hu ↦ ?_⟩
    rw [mem_singleton_iff] at hu
    rw [hu] at hne
    exact hne.elim (fun h ↦ h rfl) (fun h ↦ h rfl)
  -- a sub-rectangle avoiding `ρ` is in `K`
  have hsubK : ∀ p q : ℂ, p.re ≤ q.re → p.im ≤ q.im → z.re ≤ p.re → q.re ≤ w.re → z.im ≤ p.im →
      q.im ≤ w.im → (q.re < ρ.re ∨ ρ.re < p.re ∨ q.im < ρ.im ∨ ρ.im < p.im) →
      [[p.re, q.re]] ×ℂ [[p.im, q.im]] ⊆ K := by
    intro p q b1 b2 b3 b4 b5 b6 hne u hu
    rw [mem_rect b1 b2] at hu
    refine hmemK u (by linarith [hu.1.1]) (by linarith [hu.1.2]) (by linarith [hu.2.1])
      (by linarith [hu.2.2]) ?_
    rcases hne with h | h | h | h
    · exact Or.inl (by linarith [hu.1.2])
    · exact Or.inl (by linarith [hu.1.1])
    · exact Or.inr (by linarith [hu.2.2])
    · exact Or.inr (by linarith [hu.2.1])
  set x₁ := ρ.re - s with hx₁
  set x₂ := ρ.re + s with hx₂
  set y₁ := ρ.im - s with hy₁
  set y₂ := ρ.im + s with hy₂
  -- cut at `x₁`
  have s1 := bdry_split_re hc (c := x₁) (z := z) (w := w) (by linarith) (by linarith)
    (fun x hx ↦ hmemK _ (by simp [hx.1]) (by simp [hx.2]) (by simp) (by simp; linarith)
      (Or.inr (by simp; linarith)))
    (fun x hx ↦ hmemK _ (by simp [hx.1]) (by simp [hx.2]) (by simp; linarith) (by simp)
      (Or.inr (by simp; linarith)))
  have z1 : bdry f z (x₁ + w.im * I) = 0 :=
    bdry_eq_zero (hf.mono (hsubK _ _ (by simp; linarith) (by simp; linarith) le_rfl
      (by simp; linarith) le_rfl (by simp) (Or.inl (by simp; linarith))))
  -- cut at `x₂`
  have s2 := bdry_split_re hc (c := x₂) (z := (x₁ : ℂ) + z.im * I) (w := w) (by simp; linarith)
    (by linarith)
    (fun x hx ↦ hmemK _ (by simp at hx ⊢; linarith [hx.1]) (by simp at hx ⊢; linarith [hx.2])
      (by simp) (by simp; linarith) (Or.inr (by simp; linarith)))
    (fun x hx ↦ hmemK _ (by simp at hx ⊢; linarith [hx.1]) (by simp at hx ⊢; linarith [hx.2])
      (by simp; linarith) (by simp) (Or.inr (by simp; linarith)))
  have z2 : bdry f ((x₂ : ℂ) + ((x₁ : ℂ) + z.im * I).im * I) w = 0 :=
    bdry_eq_zero (hf.mono (hsubK _ _ (by simp; linarith) (by simp; linarith) (by simp; linarith)
      le_rfl (by simp) le_rfl (Or.inr (Or.inl (by simp; linarith)))))
  -- cut the middle strip at `y₁`
  have s3 := bdry_split_im hc (d := y₁) (z := (x₁ : ℂ) + z.im * I) (w := (x₂ : ℂ) + w.im * I)
    (by simp; linarith) (by simp; linarith)
    (fun y hy ↦ hmemK _ (by simp; linarith) (by simp; linarith) (by simp at hy ⊢; linarith [hy.1])
      (by simp at hy ⊢; linarith [hy.2]) (Or.inl (by simp; linarith)))
    (fun y hy ↦ hmemK _ (by simp; linarith) (by simp; linarith) (by simp at hy ⊢; linarith [hy.1])
      (by simp at hy ⊢; linarith [hy.2]) (Or.inl (by simp; linarith)))
  have z3 : bdry f ((x₁ : ℂ) + z.im * I) (((x₂ : ℂ) + w.im * I).re + y₁ * I) = 0 :=
    bdry_eq_zero (hf.mono (hsubK _ _ (by simp; linarith) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp) (by simp; linarith) (Or.inr (Or.inr (Or.inl
        (by simp; linarith))))))
  -- cut at `y₂`
  have s4 := bdry_split_im hc (d := y₂) (z := (((x₁ : ℂ) + z.im * I).re : ℂ) + y₁ * I)
    (w := (x₂ : ℂ) + w.im * I) (by simp; linarith) (by simp; linarith)
    (fun y hy ↦ hmemK _ (by simp; linarith) (by simp; linarith) (by simp at hy ⊢; linarith [hy.1])
      (by simp at hy ⊢; linarith [hy.2]) (Or.inl (by simp; linarith)))
    (fun y hy ↦ hmemK _ (by simp; linarith) (by simp; linarith) (by simp at hy ⊢; linarith [hy.1])
      (by simp at hy ⊢; linarith [hy.2]) (Or.inl (by simp; linarith)))
  have z4 : bdry f (((((x₁ : ℂ) + z.im * I).re : ℂ) + y₁ * I).re + y₂ * I)
      ((x₂ : ℂ) + w.im * I) = 0 :=
    bdry_eq_zero (hf.mono (hsubK _ _ (by simp; linarith) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith) (by simp) (Or.inr (Or.inr (Or.inr
        (by simp; linarith))))))
  rw [s1, z1, zero_add, s2, z2, add_zero, s3, z3, zero_add, s4, z4, add_zero]
  congr 1
  · apply Complex.ext <;> simp [hx₁, hy₁]
  · apply Complex.ext <;> simp [hx₂, hy₂]

/-! ### Induction on the set of singularities -/

/-- The residue theorem for small circles of radius `s`, when distinct real (or imaginary) parts of
points of `P` differ by more than `3s`. -/
theorem bdry_eq_sum_of_separated {f : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (P : Finset ℂ) :
    ∀ z w : ℂ, z.re < w.re → z.im < w.im →
      (∀ ρ ∈ P, z.re < ρ.re - s ∧ ρ.re + s < w.re ∧ z.im < ρ.im - s ∧ ρ.im + s < w.im) →
      (∀ ρ ∈ P, ∀ σ ∈ P, (ρ.re = σ.re ∨ 3 * s < |ρ.re - σ.re|) ∧
        (ρ.im = σ.im ∨ 3 * s < |ρ.im - σ.im|)) →
      (∀ ρ ∈ P, ∀ u : ℂ, u ≠ ρ → ‖u - ρ‖ < s * Real.exp 2 → DifferentiableAt ℂ f u) →
      DifferentiableOn ℂ f (([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ ↑P) →
      bdry f z w = ∑ ρ ∈ P, ∮ u in C(ρ, s), f u := by
  classical
  induction P using Finset.strongInduction with
  | H P ih =>
  intro z w hzw1 hzw2 hin hsep hdisc hf
  set K := ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ ↑P with hK
  have hc : ContinuousOn f K := hf.continuousOn
  have hzw1' : z.re ≤ w.re := hzw1.le
  have hzw2' : z.im ≤ w.im := hzw2.le
  -- points of the closed rectangle away from `P` are in `K`
  have hmemK : ∀ u : ℂ, z.re ≤ u.re → u.re ≤ w.re → z.im ≤ u.im → u.im ≤ w.im → u ∉ P → u ∈ K :=
    fun u a1 a2 a3 a4 hu ↦ ⟨(mem_rect hzw1' hzw2').2 ⟨⟨a1, a2⟩, a3, a4⟩, hu⟩
  rcases P.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty]
    exact bdry_eq_zero (hf.mono fun u hu ↦ ⟨hu, by simp⟩)
  obtain ⟨ρ₀, hρ₀, hmin₀⟩ := P.exists_min_image Complex.re hne
  by_cases hre : ∃ τ ∈ P, τ.re ≠ ρ₀.re
  · -- a vertical cut at `c = ρ₀.re + 3s/2`
    obtain ⟨τ, hτ, hτre⟩ := hre
    set c := ρ₀.re + 3 * s / 2 with hcdef
    have hfar : ∀ σ ∈ P, σ.re ≠ ρ₀.re → ρ₀.re + 3 * s < σ.re := by
      intro σ hσ hne'
      rcases (hsep ρ₀ hρ₀ σ hσ).1 with h | h
      · exact absurd h.symm hne'
      · rw [abs_sub_comm, abs_of_nonneg (by linarith [hmin₀ σ hσ])] at h; linarith
    have hside : ∀ σ ∈ P, σ.re < c ↔ σ.re = ρ₀.re := by
      intro σ hσ
      constructor
      · intro h; by_contra hne'; linarith [hfar σ hσ hne']
      · intro h; rw [h]; linarith
    have hτc : ρ₀.re + 3 * s < τ.re := hfar τ hτ hτre
    have hc1 : z.re ≤ c := by linarith [(hin ρ₀ hρ₀).1]
    have hc2 : c ≤ w.re := by linarith [(hin τ hτ).2.1]
    have hsplit := bdry_split_re hc (c := c) hc1 hc2
      (fun x hx ↦ hmemK _ (by simpa using hx.1) (by simpa using hx.2) (by simp) (by simp; linarith)
        (fun hP ↦ by have := (hin _ hP).2.2.1; simp at this; linarith))
      (fun x hx ↦ hmemK _ (by simpa using hx.1) (by simpa using hx.2) (by simp; linarith) (by simp)
        (fun hP ↦ by have := (hin _ hP).2.2.2; simp at this; linarith))
    have hsub₁ : P.filter (fun σ ↦ σ.re < c) ⊂ P :=
      Finset.filter_ssubset.2 ⟨τ, hτ, by rw [hside τ hτ]; exact hτre⟩
    have hsub₂ : P.filter (fun σ ↦ ¬ σ.re < c) ⊂ P :=
      Finset.filter_ssubset.2 ⟨ρ₀, hρ₀, by rw [not_not, hside ρ₀ hρ₀]⟩
    have h₁ := ih _ hsub₁ z ((c : ℂ) + w.im * I) (by simp; linarith [(hin ρ₀ hρ₀).1])
      (by simpa using hzw2)
      (fun σ hσ ↦ by
        obtain ⟨hσP, hσc⟩ := Finset.mem_filter.1 hσ
        have := hin σ hσP
        rw [hside σ hσP] at hσc
        refine ⟨this.1, ?_, this.2.2.1, by simpa using this.2.2.2⟩
        simp; linarith)
      (fun σ hσ σ' hσ' ↦ hsep σ (Finset.mem_filter.1 hσ).1 σ' (Finset.mem_filter.1 hσ').1)
      (fun σ hσ ↦ hdisc σ (Finset.mem_filter.1 hσ).1)
      (hf.mono fun u hu ↦ by
        obtain ⟨hu1, hu2⟩ := hu
        rw [mem_rect (by simp; linarith) (by simpa using hzw2')] at hu1
        simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
          mul_one, zero_add, add_zero, sub_self] at hu1
        refine ⟨(mem_rect hzw1' hzw2').2 ⟨⟨hu1.1.1, by linarith [hu1.1.2]⟩, hu1.2⟩, fun hP ↦ ?_⟩
        refine hu2 (Finset.mem_filter.2 ⟨hP, ?_⟩)
        rcases eq_or_ne u.re ρ₀.re with h | h
        · rw [h]; linarith
        · linarith [hfar u hP h, hu1.1.2])
    have h₂ := ih _ hsub₂ ((c : ℂ) + z.im * I) w (by simp; linarith [(hin τ hτ).2.1])
      (by simpa using hzw2)
      (fun σ hσ ↦ by
        obtain ⟨hσP, hσc⟩ := Finset.mem_filter.1 hσ
        have := hin σ hσP
        rw [hside σ hσP] at hσc
        have := hfar σ hσP hσc
        refine ⟨by simp; linarith, (hin σ hσP).2.1, by simpa using (hin σ hσP).2.2.1,
          (hin σ hσP).2.2.2⟩)
      (fun σ hσ σ' hσ' ↦ hsep σ (Finset.mem_filter.1 hσ).1 σ' (Finset.mem_filter.1 hσ').1)
      (fun σ hσ ↦ hdisc σ (Finset.mem_filter.1 hσ).1)
      (hf.mono fun u hu ↦ by
        obtain ⟨hu1, hu2⟩ := hu
        rw [mem_rect (by simp; linarith) (by simpa using hzw2')] at hu1
        simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
          mul_one, zero_add, add_zero, sub_self] at hu1
        refine ⟨(mem_rect hzw1' hzw2').2 ⟨⟨by linarith [hu1.1.1], hu1.1.2⟩, hu1.2⟩, fun hP ↦ ?_⟩
        exact hu2 (Finset.mem_filter.2 ⟨hP, by linarith [hu1.1.1]⟩))
    rw [hsplit, h₁, h₂, Finset.sum_filter_add_sum_filter_not]
  · simp only [ne_eq, not_exists, not_and, not_not] at hre
    obtain ⟨ρ₁, hρ₁, hmin₁⟩ := P.exists_min_image Complex.im hne
    by_cases him : ∃ τ ∈ P, τ.im ≠ ρ₁.im
    · -- a horizontal cut at `d = ρ₁.im + 3s/2`
      obtain ⟨τ, hτ, hτim⟩ := him
      set d := ρ₁.im + 3 * s / 2 with hddef
      have hfar : ∀ σ ∈ P, σ.im ≠ ρ₁.im → ρ₁.im + 3 * s < σ.im := by
        intro σ hσ hne'
        rcases (hsep ρ₁ hρ₁ σ hσ).2 with h | h
        · exact absurd h.symm hne'
        · rw [abs_sub_comm, abs_of_nonneg (by linarith [hmin₁ σ hσ])] at h; linarith
      have hside : ∀ σ ∈ P, σ.im < d ↔ σ.im = ρ₁.im := by
        intro σ hσ
        constructor
        · intro h; by_contra hne'; linarith [hfar σ hσ hne']
        · intro h; rw [h]; linarith
      have hτd : ρ₁.im + 3 * s < τ.im := hfar τ hτ hτim
      have hd1 : z.im ≤ d := by linarith [(hin ρ₁ hρ₁).2.2.1]
      have hd2 : d ≤ w.im := by linarith [(hin τ hτ).2.2.2]
      have hsplit := bdry_split_im hc (d := d) hd1 hd2
        (fun y hy ↦ hmemK _ (by simp; linarith) (by simp) (by simpa using hy.1)
          (by simpa using hy.2) (fun hP ↦ by have := (hin _ hP).2.1; simp at this; linarith))
        (fun y hy ↦ hmemK _ (by simp) (by simp; linarith) (by simpa using hy.1)
          (by simpa using hy.2) (fun hP ↦ by have := (hin _ hP).1; simp at this; linarith))
      have hsub₁ : P.filter (fun σ ↦ σ.im < d) ⊂ P :=
        Finset.filter_ssubset.2 ⟨τ, hτ, by rw [hside τ hτ]; exact hτim⟩
      have hsub₂ : P.filter (fun σ ↦ ¬ σ.im < d) ⊂ P :=
        Finset.filter_ssubset.2 ⟨ρ₁, hρ₁, by rw [not_not, hside ρ₁ hρ₁]⟩
      have h₁ := ih _ hsub₁ z ((w.re : ℂ) + d * I) (by simpa using hzw1)
        (by simp; linarith [(hin ρ₁ hρ₁).2.2.1])
        (fun σ hσ ↦ by
          obtain ⟨hσP, hσd⟩ := Finset.mem_filter.1 hσ
          have := hin σ hσP
          rw [hside σ hσP] at hσd
          refine ⟨this.1, by simpa using this.2.1, this.2.2.1, ?_⟩
          simp; linarith)
        (fun σ hσ σ' hσ' ↦ hsep σ (Finset.mem_filter.1 hσ).1 σ' (Finset.mem_filter.1 hσ').1)
        (fun σ hσ ↦ hdisc σ (Finset.mem_filter.1 hσ).1)
        (hf.mono fun u hu ↦ by
          obtain ⟨hu1, hu2⟩ := hu
          rw [mem_rect (by simpa using hzw1') (by simp; linarith)] at hu1
          simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
            mul_one, zero_add, add_zero, sub_self] at hu1
          refine ⟨(mem_rect hzw1' hzw2').2 ⟨hu1.1, ⟨hu1.2.1, by linarith [hu1.2.2]⟩⟩,
            fun hP ↦ ?_⟩
          refine hu2 (Finset.mem_filter.2 ⟨hP, ?_⟩)
          rcases eq_or_ne u.im ρ₁.im with h | h
          · rw [h]; linarith
          · linarith [hfar u hP h, hu1.2.2])
      have h₂ := ih _ hsub₂ ((z.re : ℂ) + d * I) w (by simpa using hzw1)
        (by simp; linarith [(hin τ hτ).2.2.2])
        (fun σ hσ ↦ by
          obtain ⟨hσP, hσd⟩ := Finset.mem_filter.1 hσ
          rw [hside σ hσP] at hσd
          have := hfar σ hσP hσd
          refine ⟨by simpa using (hin σ hσP).1, (hin σ hσP).2.1, by simp; linarith,
            (hin σ hσP).2.2.2⟩)
        (fun σ hσ σ' hσ' ↦ hsep σ (Finset.mem_filter.1 hσ).1 σ' (Finset.mem_filter.1 hσ').1)
        (fun σ hσ ↦ hdisc σ (Finset.mem_filter.1 hσ).1)
        (hf.mono fun u hu ↦ by
          obtain ⟨hu1, hu2⟩ := hu
          rw [mem_rect (by simpa using hzw1') (by simp; linarith)] at hu1
          simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
            mul_one, zero_add, add_zero, sub_self] at hu1
          refine ⟨(mem_rect hzw1' hzw2').2 ⟨hu1.1, ⟨by linarith [hu1.2.1], hu1.2.2⟩⟩,
            fun hP ↦ ?_⟩
          exact hu2 (Finset.mem_filter.2 ⟨hP, by linarith [hu1.2.1]⟩))
      rw [hsplit, h₁, h₂, Finset.sum_filter_add_sum_filter_not]
    · -- a single point
      simp only [ne_eq, not_exists, not_and, not_not] at him
      have hP : P = {ρ₁} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨hρ₁, fun σ hσ ↦ ?_⟩
        exact Complex.ext ((hre σ hσ).trans (hre ρ₁ hρ₁).symm) (him σ hσ)
      subst hP
      rw [Finset.sum_singleton]
      obtain ⟨a1, a2, a3, a4⟩ := hin ρ₁ (Finset.mem_singleton_self _)
      rw [bdry_eq_bdry_square hs a1 a2 a3 a4 (by simpa only [hK, Finset.coe_singleton] using hf)]
      exact bdry_square_eq_circleIntegral hs (hdisc ρ₁ (Finset.mem_singleton_self _))

/-! ### The residue theorem -/

/-- A finite set of reals has a positive lower bound for the absolute values of its nonzero
elements. -/
theorem exists_pos_le_abs (S : Finset ℝ) : ∃ g : ℝ, 0 < g ∧ ∀ v ∈ S, v = 0 ∨ g ≤ |v| := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S _ ih =>
    obtain ⟨g, hg, h⟩ := ih
    by_cases ha : a = 0
    · refine ⟨g, hg, fun v hv ↦ ?_⟩
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact Or.inl ha
      · exact h v hv
    · refine ⟨min g |a|, lt_min hg (abs_pos.2 ha), fun v hv ↦ ?_⟩
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact Or.inr (min_le_right _ _)
      · exact (h v hv).imp_right fun h' ↦ (min_le_left _ _).trans h'

/-- **The residue theorem on a rectangle**, with residues written as circle integrals. The
statement is that of `IEANTN`'s `ContourIntegration.v1.residue_theorem_rectangle`, verbatim. -/
theorem residue_theorem_rectangle :
    ∀ (z w : ℂ) (P : Finset ℂ) (r : ℝ) (f : ℂ → ℂ),
      z.re < w.re → z.im < w.im → 0 < r →
      (∀ ρ ∈ P, z.re < ρ.re - r ∧ ρ.re + r < w.re ∧ z.im < ρ.im - r ∧ ρ.im + r < w.im) →
      (∀ ρ ∈ P, ∀ σ ∈ P, ρ ≠ σ → 2 * r < dist ρ σ) →
      DifferentiableOn ℂ f ((Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) \ ↑P) →
        (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I))
          - (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I))
          + Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I))
          - Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))
          = ∑ ρ ∈ P, (∮ ζ in C(ρ, r), f ζ) := by
  intro z w P r f hzw1 hzw2 hr hin hsep hf
  classical
  set K := ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ ↑P with hK
  -- a point within `r` of a point `ρ ∈ P`, other than `ρ`, is not in `P`
  have hnotP : ∀ ρ ∈ P, ∀ u : ℂ, u ≠ ρ → ‖u - ρ‖ ≤ r → u ∉ P := by
    intro ρ hρ u hu hur huP
    have h := hsep ρ hρ u huP (Ne.symm hu)
    rw [Complex.dist_eq, norm_sub_rev] at h
    linarith
  -- ... and lies in the open rectangle
  have hbox : ∀ ρ ∈ P, ∀ u : ℂ, ‖u - ρ‖ ≤ r →
      (z.re < u.re ∧ u.re < w.re) ∧ (z.im < u.im ∧ u.im < w.im) := by
    intro ρ hρ u hur
    obtain ⟨a1, a2, a3, a4⟩ := hin ρ hρ
    have b1 := (abs_re_le_norm (u - ρ)).trans hur
    have b2 := (abs_im_le_norm (u - ρ)).trans hur
    rw [sub_re, abs_le] at b1
    rw [sub_im, abs_le] at b2
    exact ⟨⟨by linarith [b1.1], by linarith [b1.2]⟩, by linarith [b2.1], by linarith [b2.2]⟩
  have hmemK : ∀ ρ ∈ P, ∀ u : ℂ, u ≠ ρ → ‖u - ρ‖ ≤ r → u ∈ K := by
    intro ρ hρ u hu hur
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hbox ρ hρ u hur
    exact ⟨(mem_rect hzw1.le hzw2.le).2 ⟨⟨a1.le, a2.le⟩, a3.le, a4.le⟩, hnotP ρ hρ u hu hur⟩
  have hdiff : ∀ ρ ∈ P, ∀ u : ℂ, u ≠ ρ → ‖u - ρ‖ < r → DifferentiableAt ℂ f u := by
    intro ρ hρ u hu hur
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hbox ρ hρ u hur.le
    refine hf.differentiableAt (mem_nhds_iff.2 ⟨(Ioo z.re w.re ×ℂ Ioo z.im w.im) ∩ (↑P)ᶜ,
      fun v hv ↦ ⟨?_, hv.2⟩, (isOpen_Ioo.reProdIm isOpen_Ioo).inter
        P.finite_toSet.isClosed.isOpen_compl, ⟨⟨⟨a1, a2⟩, a3, a4⟩, hnotP ρ hρ u hu hur.le⟩⟩)
    obtain ⟨⟨c1, c2⟩, c3, c4⟩ := hv.1
    exact (mem_rect hzw1.le hzw2.le).2 ⟨⟨c1.le, c2.le⟩, c3.le, c4.le⟩
  -- shrink the radius
  obtain ⟨g, hg, hgap⟩ := exists_pos_le_abs
    ((P ×ˢ P).image (fun p ↦ p.1.re - p.2.re) ∪ (P ×ˢ P).image (fun p ↦ p.1.im - p.2.im))
  set s := min (r / Real.exp 2) (g / 4) with hs_def
  have hs : 0 < s := lt_min (div_pos hr (Real.exp_pos 2)) (by linarith)
  have hse : s * Real.exp 2 ≤ r := by
    rw [← le_div_iff₀ (Real.exp_pos 2)]
    exact min_le_left _ _
  have hsr : s < r := by
    have : 1 < Real.exp 2 := Real.one_lt_exp_iff.2 two_pos
    nlinarith
  have hsg : 3 * s < g := by
    have := min_le_right (r / Real.exp 2) (g / 4)
    linarith
  have key := bdry_eq_sum_of_separated (f := f) hs P z w hzw1 hzw2
    (fun ρ hρ ↦ by obtain ⟨a1, a2, a3, a4⟩ := hin ρ hρ; exact ⟨by linarith, by linarith,
      by linarith, by linarith⟩)
    (fun ρ hρ σ hσ ↦ by
      have h1 := hgap (ρ.re - σ.re) (Finset.mem_union_left _
        (Finset.mem_image.2 ⟨(ρ, σ), Finset.mem_product.2 ⟨hρ, hσ⟩, rfl⟩))
      have h2 := hgap (ρ.im - σ.im) (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨(ρ, σ), Finset.mem_product.2 ⟨hρ, hσ⟩, rfl⟩))
      refine ⟨h1.imp sub_eq_zero.1 fun h ↦ by linarith, h2.imp sub_eq_zero.1 fun h ↦ by linarith⟩)
    (fun ρ hρ u hu hus ↦ hdiff ρ hρ u hu (hus.trans_le hse)) hf
  refine key.trans (Finset.sum_congr rfl fun ρ hρ ↦ ?_)
  refine (circleIntegral_eq_of_differentiable_on_annulus_off_countable hs hsr.le
    Set.countable_empty (hf.continuousOn.mono fun u hu ↦ ?_) fun u hu ↦ ?_).symm
  · have h1 : ‖u - ρ‖ ≤ r := by simpa [dist_eq_norm] using hu.1
    have h2 : s ≤ ‖u - ρ‖ := by simpa [dist_eq_norm] using hu.2
    exact hmemK ρ hρ u (fun h ↦ by rw [h, sub_self, norm_zero] at h2; linarith) h1
  · have h1 : ‖u - ρ‖ < r := by simpa [dist_eq_norm] using hu.1.1
    have h2 : s < ‖u - ρ‖ := by simpa [dist_eq_norm] using hu.1.2
    exact hdiff ρ hρ u (fun h ↦ by rw [h, sub_self, norm_zero] at h2; linarith) h1

end ResidueRectangle
