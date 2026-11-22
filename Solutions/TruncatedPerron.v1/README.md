# TruncatedPerron.v1

This proves the three conclusions of `TruncatedPerron.v1` (`perron_single_term`, `perron_general`
and `perron_psi`) as the challenge states them, with no `sorry`. `#print axioms` on each
`challenge_*` theorem gives `[propext, Classical.choice, Quot.sound]`, and since the node doesn't
import anything, they're unconditional.

The sources are Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12; Montgomery–Vaughan,
*Multiplicative Number Theory I*, Lemma 5.1, Theorem 5.2 and the proof of Theorem 12.5; and
Davenport, *Multiplicative Number Theory*, ch. 17.

## Single term (`PerronDev.lean`)

For `c, T > 0` and `y > 0`, `y ≠ 1`, the bound is a minimum of two things, and they're proved
separately.

The `1/(πT|log y|)` part shifts the contour to a finite rectangle. When `y > 1` it goes left,
writing `y^s/s` as the entire function `(y^s − 1)/s` plus `1/s`, whose rectangle integral is
`2πi`. When `y < 1` it goes right. The far side is bounded for each width, so no limits of
integrals are needed.

The `1` part moves onto the circular arc of radius `|c + iT|`, using a primitive on a disc from
`DifferentiableOn.isExactOn_ball`.

`HIntegral`, `VIntegral`, `RectangleIntegral` and the rectangle integral of `1/s` are adapted from
PrimeNumberTheoremAnd's `ResidueCalcOnRectangles.lean` (Apache-2.0).

## General Dirichlet series (`PerronGeneral.lean`)

On the segment, `LSeries a s · x^s/s` splits as `∑ₙ aₙ (x/n)^s / s`. Each term is at most
`‖aₙ‖ (x/n)^σ₀ / σ₀`, which is summable because `abscissaOfAbsConv a < σ₀`, so dominated
convergence lets the sum and the integral swap. Then the single-term bound handles every `n ≠ x`
with `y = x/n`. For `n = x` the integral is `2·arg(σ₀ + iT)`, and `π/2 − arg(σ₀ + iT) ≤ σ₀/T`.
The right-hand series is shown to be summable, so it isn't the junk value `0`.

## The ψ case (`PerronPsi.lean`)

This applies `perron_general` with `aₙ = Λ(n)` and `σ₀ = 1 + 1/log x`, which makes
`x^σ₀ = e·x`. The constant is `C = 400`, and I haven't tried to make it small.

The `n = x` term is at most `log x / T`. When `n ≤ x/2` or `n ≥ 2x`, `|log(x/n)| ≥ log 2`, and
`Λ(n) ≤ 2 log x · n^{1/(2 log x)}`. Then the p-series bound `∑ n^{-p} ≤ 1 + 1/(p − 1)` gives
`O(x log²x / T)` for all of those terms together.

When `x/2 < n < 2x`, `|log(x/n)| ≥ |x − n|/(2x)`, so each term is at most
`16 log x · min(1, x/(T|x − n|))`. At most two prime powers are within 1 of `x`, each at distance
at least `⟨x⟩` (which is proved positive), and they give the `log x · min(1, x/(T⟨x⟩))` term. The
rest add up to a harmonic sum, which is also `O(x log²x / T)`.

## Building

Run `lake build` from this directory. A cold build takes about ten minutes, mostly Mathlib.
