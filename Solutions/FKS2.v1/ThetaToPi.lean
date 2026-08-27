/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import PsiToTheta
import IEANTN.Nodes.Buthe.v1.Conclusions
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions

/-!
# From a bound on `Eθ` to one on `Eπ`, and the headline estimate

The paper's Theorem 3, Corollary 23 and Corollary 26.

The conversion is partial summation: `π(x) − Li(x)` is an integral of `(θ(t) − t)/(t log² t)` plus
a boundary term, so an admissible bound for `Eθ` integrates to one for `Eπ`. The work is in
bounding that integral without losing the shape, which is `integral_admissibleBound_le` below.

## Where the two kinds of input enter

`Buthe.v1.theorem_2_li_minus_pi` supplies the mid-range, below `10¹⁹`, where the asymptotic bound
is not yet the best thing available.

`FKS2Numerics.v1.table6_row2_floor` supplies the small range `[e, e⁶]`, where the claim is a finite
check rather than analysis. **Upstream carries that as a `sorry`; here it is a hypothesis**, which
is the whole reason the numerical content was split into its own node.
-/

namespace FKS2Sol

open Real IEANTN

/-- The integral that partial summation produces, bounded in the same admissible shape.

This is the analytic heart of the `θ → π` step: `∫ dt / log² t` against an admissible bound has to
come back out as an admissible bound with the exponent shifted, and the constant it costs is what
turns `A = 121.0961` into Table 6's rows. -/
theorem integral_admissibleBound_le {A B C R x₀ : ℝ} (hR : 0 < R) (hx₀ : 1 < x₀)
    (h : HasClassicalBound Eθ A B C R x₀) :
    ∃ A' : ℝ, HasClassicalBound Eπ A' (B - 1) C R x₀ := by
  sorry

/-- **Theorem 3**, the general `θ → π` conversion, stated as the paper does: given an admissible
bound for `Eθ` above `x₀`, and a `π`/`θ` comparison at `x₀`, one gets an admissible bound for `Eπ`.

The `B ≥ max(3/2, 1 + C²/(16R))` hypothesis is `Growth.lean`'s again — it is what makes the
resulting bound decreasing, and so what lets a single evaluation at `x₀` extend upward. -/
theorem classicalBound_pi_of_theta
    {A B C R x₀ : ℝ} (hR : 0 < R) (hB : max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B) (hx₀ : 1 < x₀)
    (h : HasClassicalBound Eθ A B C R x₀) :
    ∃ Aπ : ℝ, HasClassicalBound Eπ Aπ B C R x₀ := by
  sorry

/-- **Corollary 23**, at the row this node states: `Eπ` obeys the classical bound with
`A = 0.826`, `B = 1/4`, `C = 1`, `R = 5.5666305`, for all `x ≥ e`.

Three ranges, and only the first is analysis. Above `10¹⁹` the conversion of Theorem 3 applied to
Corollary 14. Between `e⁶` and `10¹⁹`, Büthe's estimate. On `[e, e⁶]`, the finite check — the
threshold `x₀ = e` is exactly where that check runs out. -/
theorem corollary_23
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi)
    (hfloor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_23 := by
  sorry

/-- **Corollary 26**, the paper's headline: `|π(x) − Li(x)| ≤ 0.4298 x / log x` for all `x ≥ 2`.

Split at `e`. For `x ≥ e` this is Corollary 23 with the admissible bound compared against the
constant — the bound's maximum on `[e, ∞)` is below `0.4298`. For `2 ≤ x < e` it is direct:
`π(x) = 1`, `0 ≤ Li(x) ≤ 2`, and `log x / x ≤ 1/e`. No new input is needed for the small piece,
which is why this conclusion imports nothing that Corollary 23 does not. -/
theorem corollary_26
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi) :
    FKS2.v1.corollary_26 := by
  sorry

end FKS2Sol
