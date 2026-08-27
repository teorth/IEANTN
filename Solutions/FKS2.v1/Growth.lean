/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Growth and monotonicity

The self-contained analytic toolkit FKS2's conversions rest on: when the function

`g a b c x = x^(-a) (log x)^b exp (c √(log x))`

is eventually decreasing. Everything downstream — the `ψ → θ` conversion and the `θ → π` one — is
an application of this plus bookkeeping, which is why it is worth having in its own file.

Nothing here mentions primes, so this file is the cheapest part of the port to finish and the
right place to start. It corresponds to the paper's Lemma 10 and Corollary 11.
-/

namespace FKS2Sol

open Real

/-- `g a b c x = x^(-a) (log x)^b exp (c √(log x))`, the shape every admissible bound in FKS2
reduces to once the `log x / R` is unwound. -/
noncomputable def g (a b c x : ℝ) : ℝ :=
  x ^ (-a) * (log x) ^ b * exp (c * sqrt (log x))

/-- With `a > 0` and `b` below the critical exponent, `g` is decreasing on `(1, ∞)`.

The easy regime: the polynomial factor never gets a chance to compete with `x^{-a}`. -/
theorem g_antitone_of_lt {a b c : ℝ} (ha : 0 < a) (hb : b < -c ^ 2 / (16 * a)) :
    ∀ x y : ℝ, 1 < x → x ≤ y → g a b c y ≤ g a b c x := by
  sorry

/-- At or above the critical exponent, `g` is still eventually decreasing, but only past a
threshold that depends on the parameters.

This is the case that does the work: the threshold is where FKS2's `x₀`s come from, and getting it
right is what makes the corollaries hold from `x ≥ 2` rather than from something enormous. -/
theorem g_antitone_of_ge {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hb : -c ^ 2 / (16 * a) ≤ b) :
    ∃ X : ℝ, 1 < X ∧ ∀ x y : ℝ, X ≤ x → x ≤ y → g a b c y ≤ g a b c x := by
  sorry

/-- The negative-exponent case, needed for the `θ → π` conversion where `b < 0`. -/
theorem g_antitone_of_neg {b c : ℝ} (hb : b < 0) (hc : 0 < c) :
    ∀ x y : ℝ, 1 < x → x ≤ y → g 0 b c y ≤ g 0 b c x := by
  sorry

/-- **Corollary 11.** An admissible bound with `B > 1 + C²/(16R)` is decreasing above `1`.

The form the conversions actually use: it says an admissible bound, once established at `x₀`, keeps
falling, so a bound proved at one point extends to everything beyond it. -/
theorem admissibleBound_antitone {B C R : ℝ} (hR : 0 < R) (hB : 1 + C ^ 2 / (16 * R) < B) :
    ∀ x y : ℝ, 1 < x → x ≤ y →
      IEANTN.admissibleBound 1 B C R y ≤ IEANTN.admissibleBound 1 B C R x := by
  sorry

end FKS2Sol
