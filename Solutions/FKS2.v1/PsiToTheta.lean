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

The paper's Proposition 13 and Corollary 14. The step is arithmetic once the growth results of
`Growth.lean` are in hand: `ψ(x) − θ(x)` is bounded by `BKLNW`'s Corollary 5.1, so an admissible
bound for `Eψ` becomes one for `Eθ` at the cost of a multiplier that tends to `1`.

The multiplier is `nuAsymp` below, and the whole content of Proposition 13 is that it is small —
`6.3376 · 10⁻⁷` at `x₀ = e³⁰`, which is why `A` moves only from `121.096` to `121.0961`.

Imports arrive as hypotheses, not as `sorry`s: `FKS.v1.psi_classical_bound` for the `ψ` bound and
the two `BKLNW.v1` conclusions for the conversion and the small range. That is the difference
between this port and the upstream one.
-/

namespace FKS2Sol

open Real IEANTN

/-- The conversion multiplier of the paper's (27): how much an admissible bound for `Eψ` must be
inflated to serve for `Eθ`, given the `ψ − θ` comparison at `x₀`.

`a₁` and `a₂` are `BKLNW`'s Corollary 5.1 coefficients. Kept as explicit arguments rather than
baked in, so that the statement says what it depends on. -/
noncomputable def nuAsymp (Aψ B C R a₁ a₂ x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
    (a₁ * log x₀ * x₀ ^ (-(1 : ℝ) / 2) + a₂ * log x₀ * x₀ ^ (-(2 : ℝ) / 3))

/-- **Proposition 13.** An admissible classical bound for `Eψ` gives one for `Eθ`, with `A`
inflated by `1 + nuAsymp` and everything else unchanged.

The hypothesis `C² / (8R) < B` is what `Growth.lean` needs to know the bound is decreasing; without
it the conversion holds only above a threshold the paper then has to chase. -/
theorem classicalBound_theta_of_psi
    {Aψ B C R x₀ : ℝ} (hR : 0 < R) (hB : C ^ 2 / (8 * R) < B) (hx₀ : 1 < x₀)
    (hpsi : HasClassicalBound Eψ Aψ B C R x₀)
    (hconv : BKLNW.v1.corollary_5_1) :
    ∃ Aθ : ℝ, HasClassicalBound Eθ Aθ B C R x₀ := by
  sorry

/-- **Corollary 14**, the node's first conclusion: `Eθ` obeys the classical bound with
`A = 121.0961`, `B = 3/2`, `C = 2`, `R = 5.5666305`, for all `x ≥ 2`.

Two ranges. Above `e³⁰` this is Proposition 13 applied to `FKS`'s bound, with the multiplier
computed to be at most `6.3376 · 10⁻⁷`. Below it the asymptotic bound exceeds `1` — its minimum on
`[2, e³⁰]` is about `2.6271` at `x = 2` — so `BKLNW`'s `Eθ ≤ 1` covers the range outright. -/
theorem corollary_14
    (hpsi : FKS.v1.psi_classical_bound)
    (hconv : BKLNW.v1.corollary_5_1)
    (hsmall : BKLNW.v1.theta_error_le_one) :
    FKS2.v1.corollary_14 := by
  sorry

end FKS2Sol
