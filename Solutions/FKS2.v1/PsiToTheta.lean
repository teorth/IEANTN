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

## A `log x₀` in `ν_asymp` that (28) does not seem to need

`nuAsymp` is transcribed from the paper's (nu_asymp) verbatim, including the factor `log(x₀)` in
each of its two terms. Evaluating the paper's own (28) at `x₀` gives the same expression *without*
those factors, and `BKLNW`'s Corollary 5.1 — checked in the BKLNW source — has no logarithm in it
either: it bounds `ψ(x) - θ(x)` by `a₁x^{1/2} + a₂x^{1/3}` flat.

So the paper's `ν_asymp` appears to be about `log(x₀)` times larger than its own argument requires
(a factor of 30 at `x₀ = e³⁰`). This is the **safe** direction — a larger `ν` means a larger `A_θ`
and hence a weaker claim — so the transcription is both faithful and provable, and Corollary 14's
`121.0961` is unaffected. Recorded rather than silently tightened: narrowing a published constant
on our own initiative is exactly what this repository must not do.
-/

namespace FKS2Sol

open Real IEANTN

/-- The conversion multiplier of the paper's (27): how much an admissible bound for `Eψ` must be
inflated to serve for `Eθ`, given the `ψ - θ` comparison constants `a₁`, `a₂` at `x₀`. -/
noncomputable def nuAsymp (Aψ B C R a₁ a₂ x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
    (a₁ * log x₀ * x₀ ^ (-(1 : ℝ) / 2) + a₂ * log x₀ * x₀ ^ (-(2 : ℝ) / 3))

/-- `Eθ ≤ Eψ + (ψ - θ)/x`: the whole `ψ → θ` transfer, before any estimation.

`|θ(x) - x| = |(ψ(x) - x) - (ψ(x) - θ(x))|`, and `ψ ≥ θ` always
(`Chebyshev.theta_le_psi`), so the second difference contributes its own size. Everything after
this is about bounding `(ψ - θ)/x`. -/
theorem Etheta_le_Epsi_add {x : ℝ} (hx : 0 < x) :
    Eθ x ≤ Eψ x + (Chebyshev.psi x - Chebyshev.theta x) / x := by
  have h2 : 0 ≤ Chebyshev.psi x - Chebyshev.theta x :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have key : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
    have hre : Chebyshev.theta x - x
        = (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) := by ring
    rw [hre]
    calc |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)|
        ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
      _ = |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
          rw [abs_of_nonneg h2]
  unfold Eθ Eψ
  rw [← add_div]
  gcongr

/-- The one remaining piece of Proposition 13: the `ψ - θ` correction, divided by `x`, is absorbed
by inflating `A` from `Aψ` to `Aψ(1 + nuAsymp …)`.

**This is where `C²/(8R) < B` earns its place.** Dividing through by
`(log x / R)^B exp(-C√(log x / R))`, the claim is that

`a₁ R^B g(1/2, -B, C/√R, x) + a₂ R^B g(2/3, -B, C/√R, x) ≤ Aψ · nuAsymp …`

with `g` as in `Growth.lean`. Both `g`s are decreasing — Lemma 10(a) at `a = 1/2` needs
`-B < -C²/(8R)`, which is the hypothesis, and at `a = 2/3` it needs only `-B < -3C²/(32R)`, which
is weaker — so each is largest at `x₀`, where the sum is `nuAsymp` by definition.

That the `x₀` evaluation is `nuAsymp` is where the paper's spare `log x₀` sits; see the module
docstring. It makes the right-hand side larger, so it costs nothing here. -/
theorem correction_le {Aψ B C R a₁ a₂ x₀ : ℝ} (hR : 0 < R) (hAψ : 0 < Aψ)
    (hB : C ^ 2 / (8 * R) < B) (hx₀ : 1 < x₀) {x : ℝ} (hx : x₀ ≤ x) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) :
    (a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3)) / x
      ≤ admissibleBound (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x
        - admissibleBound Aψ B C R x := by
  sorry

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
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hcmp : ∀ x ≥ x₀, Chebyshev.psi x - Chebyshev.theta x ≤
      a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3))
    (hpsi : HasClassicalBound Eψ Aψ B C R x₀) :
    HasClassicalBound Eθ (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x₀ := by
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by linarith) hx
  calc Eθ x ≤ Eψ x + (Chebyshev.psi x - Chebyshev.theta x) / x := Etheta_le_Epsi_add hx0
    _ ≤ admissibleBound Aψ B C R x + (a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3)) / x := by
        gcongr
        · exact hpsi x hx
        · exact hcmp x hx
    _ ≤ admissibleBound (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x := by
        linarith [correction_le hR hAψ hB hx₀ hx ha₁ ha₂]

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
