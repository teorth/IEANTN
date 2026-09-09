/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `|psi(x) - log x| <= 1/x` on the positive reals

Section 8's `lem:moruno` splits the integrand by the functional equation, and what is left is
`zeta'/zeta(t) + psi(t) + 1/t - log 2*pi` for real `t >= 2`. The digamma term needs an explicit
bound, and `GammaAsymptotics.v2` states its conclusion as an `O`-statement with an unnamed
constant, which is no use for an explicit estimate.

**So the explicit form is reproved here, copied from that node's own solution**, where it is
`abs_deriv_log_Gamma_sub_log_le` together with the bridge `digamma_ofReal`. Nothing here is new;
the duplication is deliberate and cheap, and the alternative -- a new version of a green node --
would cost a receipt for no mathematical gain.

The argument uses log-convexity alone: `Real.convexOn_log_Gamma` makes `psi` monotone, the slope
of `log Gamma` across `[x, x+1]` is exactly `log x` because `Gamma(x+1) = x Gamma(x)`, and the mean
value theorem puts that slope between `psi(x)` and `psi(x+1) = psi(x) + 1/x`.

Mathlib has no `Real.digamma`, so the real derivative is spelled `deriv (fun t => log (Gamma t))`
throughout, and `digamma_ofReal` is the one step to `Complex.digamma`.
-/

namespace CH2Digamma


open Real Set

/-- `log ∘ Γ` is differentiable on the positive reals. -/
theorem differentiableAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun t ↦ Real.log (Real.Gamma t)) x := by
  have hΓ : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun m ↦ by
      intro hcon
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hcon] at hx
      linarith)
  exact (Real.differentiableAt_log (Real.Gamma_pos_of_pos hx).ne').comp x hΓ

/-- The slope of `log Γ` across `[x, x+1]` is `log x`. -/
theorem log_Gamma_add_one_sub {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) = Real.log x := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

/-- **The recurrence**, `ψ(x+1) = ψ(x) + 1/x`, by differentiating
`log Γ(t+1) = log t + log Γ(t)` — an identity that holds on a whole neighbourhood of `x`, which
is what lets the derivatives be compared. -/
theorem deriv_log_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)
      = deriv (fun t ↦ Real.log (Real.Gamma t)) x + 1 / x := by
  have hpos : {t : ℝ | 0 < t} ∈ nhds x :=
    (isOpen_lt continuous_const continuous_id).mem_nhds hx
  have hEq : (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      =ᶠ[nhds x] (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1))) := by
    filter_upwards [hpos] with t ht
    rw [Real.Gamma_add_one (ne_of_gt ht), Real.log_mul (ne_of_gt ht)
      (Real.Gamma_pos_of_pos ht).ne']
  -- The left side, differentiated through the shift.
  have hL : HasDerivAt (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1)))
      (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := by
    have hshift : HasDerivAt (fun t : ℝ ↦ t + 1) 1 x := (hasDerivAt_id x).add_const 1
    have hout := (differentiableAt_log_Gamma (by linarith : (0:ℝ) < x + 1)).hasDerivAt
    simpa [Function.comp_def] using hout.comp x hshift
  -- The right side, differentiated termwise.
  have hR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      (x⁻¹ + deriv (fun t ↦ Real.log (Real.Gamma t)) x) x :=
    (Real.hasDerivAt_log hx.ne').add (differentiableAt_log_Gamma hx).hasDerivAt
  have hLR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := hL.congr_of_eventuallyEq hEq
  have := hLR.unique hR
  rw [this, one_div]
  ring

/-- `ψ` is monotone on the positive reals, because `log Γ` is convex there. -/
theorem monotoneOn_deriv_log_Gamma :
    MonotoneOn (deriv (fun t ↦ Real.log (Real.Gamma t))) (Ioi 0) :=
  Real.convexOn_log_Gamma.monotoneOn_deriv (fun _ hx ↦ differentiableAt_log_Gamma hx)

/-- **The squeeze**: `ψ(x) ≤ log x ≤ ψ(x+1)`. -/
theorem deriv_log_Gamma_le_log_le {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x ∧
      Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
  have hsub : Icc x (x + 1) ⊆ Ioi 0 := fun t ht ↦ lt_of_lt_of_le hx ht.1
  have hcont : ContinuousOn (fun t ↦ Real.log (Real.Gamma t)) (Icc x (x + 1)) := fun t ht ↦
    (differentiableAt_log_Gamma (hsub ht)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcs⟩ :=
    exists_deriv_eq_slope (fun t ↦ Real.log (Real.Gamma t)) (by linarith) hcont
      (fun t ht ↦ (differentiableAt_log_Gamma (lt_trans hx ht.1)).differentiableWithinAt)
  have hslope : (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) / (x + 1 - x)
      = Real.log x := by
    rw [add_sub_cancel_left, div_one, log_Gamma_add_one_sub hx]
  rw [hslope] at hcs
  have hcpos : (0 : ℝ) < c := lt_trans hx hc.1
  have h1 : deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x := by
    rw [← hcs]
    exact monotoneOn_deriv_log_Gamma (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hcpos) hc.1.le
  have h2 : Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
    rw [← hcs]
    exact monotoneOn_deriv_log_Gamma (Set.mem_Ioi.mpr hcpos)
      (Set.mem_Ioi.mpr (by linarith)) hc.2.le
  exact ⟨h1, h2⟩

/-- **`|ψ(x) − log x| ≤ 1/x` for real `x > 0`**, with the constant explicit and equal to `1`. -/
theorem abs_deriv_log_Gamma_sub_log_le {x : ℝ} (hx : 0 < x) :
    |deriv (fun t ↦ Real.log (Real.Gamma t)) x - Real.log x| ≤ 1 / x := by
  obtain ⟨hle, hge⟩ := deriv_log_Gamma_le_log_le hx
  rw [deriv_log_Gamma_add_one hx] at hge
  rw [abs_le]
  constructor <;> linarith




open Complex

/-- A complex-differentiable `f` agreeing with a real `g` on `ℝ` has `g`'s derivative there.

Reproved from Mathlib's `private HasDerivAt.complex_of_real`. -/
theorem hasDerivAt_complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

/-- A positive real is not a pole of `Γ`. -/
theorem ofReal_ne_neg_natCast {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have hx' : x = -(m : ℝ) := by exact_mod_cast h
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem differentiableAt_real_Gamma {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ Real.Gamma x :=
  Real.differentiableAt_Gamma (fun m ↦ by
    intro hcon
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hcon] at hx
    linarith)

/-- `Γ` differentiated along the real axis is the real `Γ'`. -/
theorem hasDerivAt_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    HasDerivAt Complex.Gamma ((deriv Real.Gamma x : ℝ) : ℂ) (x : ℂ) :=
  hasDerivAt_complex_of_real
    (Complex.differentiableAt_Gamma _ (ofReal_ne_neg_natCast hx))
    (differentiableAt_real_Gamma hx).hasDerivAt
    Complex.Gamma_ofReal

/-- The real logarithmic derivative of `Γ`, in the form `Γ'/Γ`. -/
theorem deriv_log_Gamma_eq {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) x = deriv Real.Gamma x / Real.Gamma x := by
  have hpos := Real.Gamma_pos_of_pos hx
  have h := (Real.hasDerivAt_log hpos.ne').comp x (differentiableAt_real_Gamma hx).hasDerivAt
  simp only [Function.comp_def] at h
  rw [h.deriv]
  ring

/-- **`Complex.digamma` on the positive real axis is Stage 1's real derivative.** -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv (fun t ↦ Real.log (Real.Gamma t)) x : ℝ) : ℂ) := by
  have hpos := Real.Gamma_pos_of_pos hx
  rw [Complex.digamma_def, logDeriv_apply, (hasDerivAt_Gamma_ofReal hx).deriv,
    Complex.Gamma_ofReal, deriv_log_Gamma_eq hx]
  push_cast
  ring


/-- **`‖psi(t) - log t‖ <= 1/t` for real `t > 0`, in the complex spelling.** -/
theorem norm_digamma_sub_log_le {t : ℝ} (ht : 0 < t) :
    ‖Complex.digamma (t : ℂ) - ((Real.log t : ℝ) : ℂ)‖ ≤ 1 / t := by
  rw [digamma_ofReal ht, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_deriv_log_Gamma_sub_log_le ht

end CH2Digamma
