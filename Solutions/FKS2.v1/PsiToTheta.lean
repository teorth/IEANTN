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

/-- Peeling the common factor off `g`: `x^{-a} = g a (-B) c x · (log x)^B exp(-c√(log x))`.

The two exponential/power factors cancel exactly, which is what lets an inequality about the
admissible bound be turned into one about `g`, where `Growth.lean` applies. -/
theorem rpow_neg_eq_g_mul {a B c x : ℝ} (hx : 1 < x) :
    x ^ (-a) = g a (-B) c x * ((log x) ^ B * exp (-c * sqrt (log x))) := by
  have hlog : 0 < log x := log_pos hx
  have h1 : (log x) ^ (-B) * (log x) ^ B = 1 := by
    rw [← rpow_add hlog]; simp
  have h2 : exp (c * sqrt (log x)) * exp (-c * sqrt (log x)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  unfold g
  have hre : x ^ (-a) * (log x) ^ (-B) * exp (c * sqrt (log x)) *
      ((log x) ^ B * exp (-c * sqrt (log x)))
      = x ^ (-a) * ((log x) ^ (-B) * (log x) ^ B) *
        (exp (c * sqrt (log x)) * exp (-c * sqrt (log x))) := by ring
  rw [hre, h1, h2, mul_one, mul_one]

/-- The admissible bound in the same factored form, `A · R^{-B} · (log x)^B exp(-(C/√R)√(log x))`.

`(log x / R)^B` splits as `(log x)^B R^{-B}`, and `(log x / R)^{1/2}` as `√(log x)/√R`, which is
where the `C/√R` throughout `Growth.lean` comes from. -/
theorem admissibleBound_eq_g_mul {A B C R x : ℝ} (hR : 0 < R) (hx : 1 < x) :
    admissibleBound A B C R x
      = A * R ^ (-B) * ((log x) ^ B * exp (-(C / sqrt R) * sqrt (log x))) := by
  have hlog : 0 < log x := log_pos hx
  unfold admissibleBound
  rw [div_rpow hlog.le hR.le, ← sqrt_eq_rpow, sqrt_div hlog.le, rpow_neg hR.le]
  have : -C * (sqrt (log x) / sqrt R) = -(C / sqrt R) * sqrt (log x) := by ring
  rw [this]
  field_simp

/-- The one remaining piece of Proposition 13: the `ψ - θ` correction, divided by `x`, is absorbed
by inflating `A` from `Aψ` to `Aψ(1 + nuAsymp …)`.

**This is where `C²/(8R) < B` earns its place.** Dividing through by the common positive factor,
the claim is that

`a₁ g(1/2, -B, C/√R, x) + a₂ g(2/3, -B, C/√R, x) ≤ log x₀ · (the same at x₀)`

with `g` as in `Growth.lean`. Both `g`s are decreasing — Lemma 10(a) at `a = 1/2` needs
`-B < -C²/(8R)`, which is exactly the hypothesis, and at `a = 2/3` it needs only `-B < -3C²/(32R)`,
which is weaker — so each is largest at `x₀`.

**`exp 1 ≤ x₀` is required, and the paper does not say so.** The `log x₀` on the right is the spare
factor discussed in the module docstring, and it is only spare when `log x₀ ≥ 1`. Below `e` it
becomes a deficit and the statement is false: take `x = x₀`, `a₁ = 1`, `a₂ = 0`, and the claim
reduces to `1 ≤ log x₀`. So Proposition 13, with the `ν_asymp` the paper prints, holds for
`x₀ ≥ e` and not below. Corollary 14 uses `x₀ = e³⁰`, so nothing downstream is affected. -/
theorem correction_le {Aψ B C R a₁ a₂ x₀ : ℝ} (hR : 0 < R) (hAψ : 0 < Aψ)
    (hB : C ^ 2 / (8 * R) < B) (hx₀ : exp 1 ≤ x₀) {x : ℝ} (hx : x₀ ≤ x)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) :
    (a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3)) / x
      ≤ admissibleBound (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x
        - admissibleBound Aψ B C R x := by
  have he1 : (1 : ℝ) < exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hx₀1 : 1 < x₀ := lt_of_lt_of_le he1 hx₀
  have hx1 : 1 < x := lt_of_lt_of_le hx₀1 hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hx₀pos : (0 : ℝ) < x₀ := by linarith
  have hlog₀ : 0 < log x₀ := log_pos hx₀1
  have hlogx : 0 < log x := log_pos hx1
  have hlog₀1 : 1 ≤ log x₀ := by
    rw [show (1 : ℝ) = log (exp 1) from (log_exp 1).symm]
    exact log_le_log (exp_pos 1) hx₀
  set c := C / sqrt R with hc
  have hc2 : c ^ 2 = C ^ 2 / R := by rw [hc, div_pow, sq_sqrt hR.le]
  set K := (log x) ^ B * exp (-c * sqrt (log x)) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  -- the left-hand side, factored
  have e1 : x ^ ((1 : ℝ) / 2) / x = x ^ (-((1 : ℝ) / 2)) := by
    have h := rpow_sub hxpos ((1 : ℝ) / 2) 1
    rw [rpow_one] at h
    rw [← h]; norm_num
  have e2 : x ^ ((1 : ℝ) / 3) / x = x ^ (-((2 : ℝ) / 3)) := by
    have h := rpow_sub hxpos ((1 : ℝ) / 3) 1
    rw [rpow_one] at h
    rw [← h]; norm_num
  have hLHS : (a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3)) / x
      = a₁ * (g (1/2) (-B) c x * K) + a₂ * (g (2/3) (-B) c x * K) := by
    rw [add_div, mul_div_assoc, mul_div_assoc, e1, e2, hK,
      ← rpow_neg_eq_g_mul (a := (1:ℝ)/2) (B := B) (c := c) hx1,
      ← rpow_neg_eq_g_mul (a := (2:ℝ)/3) (B := B) (c := c) hx1]
  -- the right-hand side, factored
  have hRHS : admissibleBound (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x
      - admissibleBound Aψ B C R x
      = (Aψ * nuAsymp Aψ B C R a₁ a₂ x₀ * R ^ (-B)) * K := by
    rw [admissibleBound_eq_g_mul hR hx1, admissibleBound_eq_g_mul hR hx1, hK]; ring
  rw [hLHS, hRHS]
  -- `Aψ ν R^{-B}` is `log x₀` times the same combination evaluated at `x₀`
  have hP : (0 : ℝ) < R ^ B := rpow_pos_of_pos hR B
  have hQ : (0 : ℝ) < (log x₀) ^ B := rpow_pos_of_pos hlog₀ B
  have hν : Aψ * nuAsymp Aψ B C R a₁ a₂ x₀ * R ^ (-B)
      = log x₀ * (a₁ * g (1/2) (-B) c x₀ + a₂ * g (2/3) (-B) c x₀) := by
    unfold nuAsymp g
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, show (-(2:ℝ)/3) = -((2:ℝ)/3) by ring,
      div_rpow hR.le hlog₀.le, sqrt_div hlog₀.le,
      show C * (sqrt (log x₀) / sqrt R) = c * sqrt (log x₀) by rw [hc]; ring,
      rpow_neg hR.le, rpow_neg hlog₀.le]
    field_simp
  rw [hν]
  -- both `g`s are decreasing, by Lemma 10(a)
  have hanti : ∀ a : ℝ, 0 < a → -B < -(c ^ 2 / (16 * a)) →
      g a (-B) c x ≤ g a (-B) c x₀ := by
    intro a hapos hlt
    have hstrict : StrictAntiOn (g a (-B) c) (Set.Ioi 1) :=
      g_strictAntiOn_of_lt hapos (by rw [neg_div]; exact hlt)
    rcases eq_or_lt_of_le hx with h | h
    · rw [h]
    · exact (hstrict (Set.mem_Ioi.mpr hx₀1) (Set.mem_Ioi.mpr hx1) h).le
  have hm1 : g (1/2) (-B) c x ≤ g (1/2) (-B) c x₀ := by
    refine hanti _ (by norm_num) ?_
    rw [hc2]
    have : C ^ 2 / R / (16 * (1/2)) = C ^ 2 / (8 * R) := by
      field_simp; ring
    rw [this]; linarith
  have hm2 : g (2/3) (-B) c x ≤ g (2/3) (-B) c x₀ := by
    refine hanti _ (by norm_num) ?_
    rw [hc2]
    have hkey : C ^ 2 / (8 * R) - C ^ 2 / R / (16 * (2/3)) = C ^ 2 / (32 * R) := by
      field_simp; ring
    have hpos : 0 ≤ C ^ 2 / (32 * R) := by positivity
    linarith
  have hg₁ : 0 ≤ g (1/2) (-B) c x₀ := by unfold g; positivity
  have hg₂ : 0 ≤ g (2/3) (-B) c x₀ := by unfold g; positivity
  have hsum : a₁ * g (1/2) (-B) c x + a₂ * g (2/3) (-B) c x
      ≤ log x₀ * (a₁ * g (1/2) (-B) c x₀ + a₂ * g (2/3) (-B) c x₀) := by
    nlinarith [mul_le_mul_of_nonneg_left hm1 ha₁, mul_le_mul_of_nonneg_left hm2 ha₂,
      mul_nonneg ha₁ hg₁, mul_nonneg ha₂ hg₂]
  calc a₁ * (g (1/2) (-B) c x * K) + a₂ * (g (2/3) (-B) c x * K)
      = (a₁ * g (1/2) (-B) c x + a₂ * g (2/3) (-B) c x) * K := by ring
    _ ≤ (log x₀ * (a₁ * g (1/2) (-B) c x₀ + a₂ * g (2/3) (-B) c x₀)) * K :=
        mul_le_mul_of_nonneg_right hsum hKpos.le

/-- **Proposition 13.** An admissible classical bound for `Eψ` gives one for `Eθ`, with `A`
inflated to `Aψ (1 + nuAsymp …)` and `B`, `C`, `R`, `x₀` unchanged.

The hypothesis `C² / (8R) < B` is the paper's, and it is what `Growth.lean` needs: it makes the
two functions `g(1/2, -B, C/√R, ·)` and `g(2/3, -B, C/√R, ·)` of the paper's (28) decreasing, so
that evaluating the correction at `x₀` bounds it everywhere above `x₀`. Without it the conversion
holds only above a threshold the paper would then have to chase.

Note `C²/(8R)`, not `C²/(16R)`: the binding case is `g(1/2, …)`, where Lemma 10(a)'s
`b < -c²/(16a)` at `a = 1/2`, `b = -B`, `c = C/√R` reads `-B < -C²/(8R)`. -/
theorem classicalBound_theta_of_psi
    {Aψ B C R a₁ a₂ x₀ : ℝ} (hR : 0 < R) (hAψ : 0 < Aψ) (hB : C ^ 2 / (8 * R) < B)
    (hx₀ : exp 1 ≤ x₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hcmp : ∀ x ≥ x₀, Chebyshev.psi x - Chebyshev.theta x ≤
      a₁ * x ^ ((1 : ℝ) / 2) + a₂ * x ^ ((1 : ℝ) / 3))
    (hpsi : HasClassicalBound Eψ Aψ B C R x₀) :
    HasClassicalBound Eθ (Aψ * (1 + nuAsymp Aψ B C R a₁ a₂ x₀)) B C R x₀ := by
  intro x hx
  have he1 : (1 : ℝ) < exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hx0 : (0 : ℝ) < x := by linarith [he1.trans_le hx₀, hx₀.trans hx]
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
