/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Growth
import IEANTN.Nodes.FKS.v1.Conclusions
import IEANTN.Nodes.BKLNW.v1.Conclusions
import IEANTN.Nodes.FKS2.v1.Conclusions

/-!
# From a bound on `Eψ` to one on `Eθ`

The paper's Proposition 13 and Corollary 14.

`ψ(x) - θ(x)` is bounded by `BKLNW`'s Corollary 5.1, so an admissible bound for `Eψ` becomes one
for `Eθ` at the cost of a multiplier that tends to `1`. The multiplier is `nuAsymp` below, and the
whole content of Proposition 13 is that it is small — `6.3376 · 10⁻⁷` at `x₀ = e³⁰`, which is why
`A` moves only from `121.096` to `121.0961`.

## The conclusion is explicit, and that is the point

Proposition 13 concludes with a *named* constant, `A_θ = A_ψ(1 + ν_asymp(x₀))`, not merely that
some constant works. Corollary 14 needs the actual number — an existential would not let it get
from `121.096` to `121.0961`. Compare `Growth.lean`'s Lemma 10(b), where the same issue arises
around the threshold.

## Why the `ψ - θ` comparison is a hypothesis rather than a `BKLNW` import here

The paper says only that "`a₁, a₂` are defined in [BKLNW, Corollary 5.1]". Proposition 13 is a
general conversion, so it takes the comparison abstractly and `corollary_14` supplies `BKLNW`'s
instance. That keeps the analytic content separable from the particular pair of constants, which
is what a later pipelined version will want.

Note the exponents. `BKLNW` bounds `ψ(x) - θ(x)` by `a₁ x^{1/2} + a₂ x^{1/3}`; dividing by `x` —
which is what the normalised error terms do — gives the `x^{-1/2}` and `x^{-2/3}` appearing in
`nuAsymp`. The `2/3` is not a typo for `1/3`.
-/

namespace FKS2Sol

open Real IEANTN

/-- The conversion multiplier of the paper's (27): how much an admissible bound for `Eψ` must be
inflated to serve for `Eθ`, given the `ψ - θ` comparison constants `a₁`, `a₂` at `x₀`. -/
noncomputable def nuAsymp (Aψ B C R a₁ a₂ x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
    (a₁ * log x₀ * x₀ ^ (-(1 : ℝ) / 2) + a₂ * log x₀ * x₀ ^ (-(2 : ℝ) / 3))

/-- **Proposition 13.** An admissible classical bound for `Eψ` gives one for `Eθ`, with `A`
inflated to `Aψ (1 + nuAsymp …)` and `B`, `C`, `R`, `x₀` unchanged.

The hypothesis `C² / (8R) < B` is the paper's, and it is what `Growth.lean` needs: it makes the
two functions `g(1/2, -B, C/√R, ·)` and `g(2/3, -B, C/√R, ·)` of the paper's (28) decreasing, so
that evaluating the correction at `x₀` bounds it everywhere above `x₀`. Without it the conversion
holds only above a threshold the paper would then have to chase.

Note `C²/(8R)`, not `C²/(16R)`: the binding case is `g(1/2, …)`, where Lemma 10(a)'s
`b < -c²/(16a)` at `a = 1/2`, `b = -B`, `c = C/√R` reads `-B < -C²/(8R)`. -/
theorem classicalBound_theta_of_psi
    {Aψ B C R a₁ a₂ x₀ : ℝ} (hR : 0 < R) (hAψ : 0 < Aψ) (hB : C ^ 2 / (8 * R) < B) (hx₀ : 1 < x₀)
    (hcmp : ∀ x ≥ x₀, Chebyshev.psi x - Chebyshev.theta x ≤
      a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3))
    (hpsi : HasClassicalBound Eψ Aψ B C R x₀) :
    HasClassicalBound Eθ (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x₀ := by
  sorry

/-- **Corollary 14**, the node's first conclusion: `Eθ` obeys the classical bound with
`A = 121.0961`, `B = 3/2`, `C = 2`, `R = 5.5666305`, for all `x ≥ 2`.

Two ranges. Above `e³⁰` this is Proposition 13 applied to `FKS`'s bound, with the multiplier
computed to be at most `6.3376 · 10⁻⁷`. Below it the asymptotic bound exceeds `1` — its minimum on
`[2, e³⁰]` is about `2.6271` at `x = 2` — so `BKLNW`'s `Eθ ≤ 1` covers the range outright.

`BKLNW.v1.corollary_5_1` is applied at `b = 30`, which is in its range `7 ≤ b ≤ 38 log 10`. -/
theorem corollary_14
    (hpsi : FKS.v1.psi_classical_bound)
    (hconv : BKLNW.v1.corollary_5_1)
    (hsmall : BKLNW.v1.theta_error_le_one) :
    FKS2.v1.corollary_14 := by
  sorry

end FKS2Sol
