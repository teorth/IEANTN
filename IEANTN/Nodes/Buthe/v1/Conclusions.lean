/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `Buthe.v1`

Jan Büthe, *An analytic method for bounding `ψ(x)`*, Math. Comp. **87** (2018), 1991–2009.

Numerical estimates for the Chebyshev functions and for `π` on `[1, 10¹⁹]`, obtained by an analytic
method resting on a verification of the Riemann hypothesis to a finite height. This is the node
that covers the low range for everything downstream: `FKS2`'s Corollaries 23 and 26 both use
Theorem 2 below `10¹⁹` and their own machinery above it.

**These are `li`, not `Li`.** Büthe states (1.9) and (1.10) against the un-offset logarithmic
integral. The two differ by `li 2 ≈ 1.045`, which is not negligible at the precision of the
constants here, and `FKS2` works with `Li` — so a downstream node consuming these must do the
conversion rather than assume it away. The Vocabulary docstrings for `li` and `Li` carry the same
warning; this is the first node where it bites.
-/

namespace Buthe.v1

open IEANTN
open scoped Chebyshev

/-- **Theorem 2, equation (1.5).** `|x − ψ(x)| ≤ 0.94 √x` for `11 < x ≤ 10¹⁹`. -/
def theorem_2_psi : Prop :=
  ∀ x : ℝ, 11 < x → x ≤ 10 ^ (19 : ℕ) → |x - Chebyshev.psi x| ≤ 0.94 * Real.sqrt x

/-- **Theorem 2, equation (1.6).** `x − θ(x) ≤ 1.95 √x` for `1423 ≤ x ≤ 10¹⁹`.

Note this is one-sided, and that (1.7) supplies the matching `x − θ(x) > 0.05 √x` on `[1, 10¹⁹]`;
a two-sided bound needs both. -/
def theorem_2_theta : Prop :=
  ∀ x : ℝ, 1423 ≤ x → x ≤ 10 ^ (19 : ℕ) → x - Chebyshev.theta x ≤ 1.95 * Real.sqrt x

/-- **Theorem 2, equation (1.9).** For `2 ≤ x ≤ 10¹⁹`,
`li(x) − π(x) ≤ (√x / log x) (1.95 + 3.9 / log x + 19.5 / (log x)²)`.

The estimate `FKS2`'s Corollary 26 uses on `[97, 10¹⁹]`: dividing through by `x / log x` turns the
right-hand side into `(1.95 + 3.9/log x + 19.5/(log x)²) / √x`, which is what that proof compares
against `0.4298`. -/
def theorem_2_li_minus_pi : Prop :=
  ∀ x : ℝ, 2 ≤ x → x ≤ 10 ^ (19 : ℕ) →
    li x - primeCounting x ≤
      Real.sqrt x / Real.log x *
        (1.95 + 3.9 / Real.log x + 19.5 / (Real.log x) ^ (2 : ℕ))

/-- **Theorem 2, equation (1.10).** `li(x) − π(x) > 0` for `2 ≤ x ≤ 10¹⁹`.

Together with (1.9) this makes the bound two-sided, which is what a statement about `|li − π|`
needs. Büthe notes that it also pushes the lower bound for the Skewes number to `10¹⁹`. -/
def theorem_2_li_gt_pi : Prop :=
  ∀ x : ℝ, 2 ≤ x → x ≤ 10 ^ (19 : ℕ) → 0 < li x - primeCounting x

end Buthe.v1
