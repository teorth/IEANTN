/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# The Dawson function

`D₊(x) = e^{-x²} ∫₀ˣ e^{t²} dt`, the paper's (Dawson).

It appears because the substitution `u = √(log t)` turns the integral of an admissible bound into
`∫ u^{2B-3} exp(u² - Cu/√R) du`, and bounding `u^{2B-3}` by its maximum leaves exactly a Dawson
integral. So `D₊` is not decoration: it is what the `θ → π` conversion's constant is made of, and
Theorem 3 cannot even be *stated* without it.

Mathlib has no Dawson function, so it is defined here.

## What is needed of it, and what is not

Theorem 3 only ever *evaluates* `D₊`, so for its statement nothing is required beyond the
definition. The paper additionally records that `D₊` has a single maximum near `0.9241` and
decreases after it, which its proof uses to bound the tail.

That fact rests on the differential equation `D₊'(x) + 2x D₊(x) = 1`, which is proved below —
`hasDerivAt_dawson`. Given it, the paper's argument is short: at a critical point `D₊(x) = 1/(2x)`,
so `D₊''(x) = -1/x`, making every positive critical point a strict local maximum; there can
therefore be only one, and `D₊` decreases after it. The maximum's location is then a numerical
question, and only that part is a computation.
-/

namespace FKS2Sol

open Real

/-- `dawson x = e^{-x²} ∫₀ˣ e^{t²} dt`, the Dawson function `D₊` of the paper's (Dawson). -/
noncomputable def dawson (x : ℝ) : ℝ :=
  exp (-x ^ 2) * ∫ t in (0 : ℝ)..x, exp (t ^ 2)

/-- `D₊` is nonnegative on `[0, ∞)`, which is the only range the conversion evaluates it on. -/
theorem dawson_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ dawson x :=
  mul_nonneg (exp_pos _).le
    (intervalIntegral.integral_nonneg hx fun _ _ ↦ (exp_pos _).le)

theorem continuous_exp_sq : Continuous fun t : ℝ => exp (t ^ 2) :=
  Real.continuous_exp.comp (continuous_pow 2)

theorem dawson_pos {x : ℝ} (hx : 0 < x) : 0 < dawson x :=
  mul_pos (exp_pos _)
    (intervalIntegral.intervalIntegral_pos_of_pos_on
      (continuous_exp_sq.intervalIntegrable 0 x) (fun _ _ ↦ exp_pos _) hx)

/-- **The Dawson differential equation**, `D₊'(x) = 1 - 2x·D₊(x)`.

The paper states it in the form `F'(x) + 2xF(x) = 1` and derives from it that `D₊` has a single
maximum, after which it decreases — the fact its tail estimate needs. Everything here is the
fundamental theorem of calculus applied to a continuous integrand, plus the product rule. -/
theorem hasDerivAt_dawson (x : ℝ) : HasDerivAt dawson (1 - 2 * x * dawson x) x := by
  have hI : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, exp (t ^ 2)) (exp (x ^ 2)) x :=
    (continuous_exp_sq.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hE : HasDerivAt (fun y : ℝ => exp (-y ^ 2)) (exp (-x ^ 2) * -(2 * x)) x := hsq.neg.exp
  have hkey : exp (-x ^ 2) * exp (x ^ 2) = 1 := by rw [← Real.exp_add]; simp
  have hval : exp (-x ^ 2) * -(2 * x) * (∫ t in (0 : ℝ)..x, exp (t ^ 2))
      + exp (-x ^ 2) * exp (x ^ 2) = 1 - 2 * x * dawson x := by
    unfold dawson; rw [hkey]; ring
  exact hval ▸ hE.mul hI

/-- `D₊` is differentiable everywhere, an immediate consequence. -/
theorem differentiable_dawson : Differentiable ℝ dawson :=
  fun x ↦ (hasDerivAt_dawson x).differentiableAt

end FKS2Sol
