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

Theorem 3 only ever *evaluates* `D₊`, so for the statements below nothing is required beyond the
definition. The paper additionally records that `D₊` has a single maximum near `0.9241` and
decreases after it, which its proof uses to bound the tail; that fact is stated where it is needed
rather than here, since proving it needs the differential equation `D₊'(x) + 2x D₊(x) = 1`.
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

end FKS2Sol
