# TruncatedPerron.v1: the truncated Perron formula

This solution proves all three conclusions of `TruncatedPerron.v1` exactly as the challenge states
them, with no `sorry`:

```lean
theorem TruncatedPerron.v1.challenge_perron_single_term : TruncatedPerron.v1.perron_single_term
theorem TruncatedPerron.v1.challenge_perron_general : TruncatedPerron.v1.perron_general
theorem TruncatedPerron.v1.challenge_perron_psi : TruncatedPerron.v1.perron_psi
```

`#print axioms` on each gives `[propext, Classical.choice, Quot.sound]`. The node imports no other
node, so these are unconditional.

Each conclusion is derived from the one before it: `perron_general` uses `perron_single_term`, and
`perron_psi` uses `perron_general`. No other node's proof is used.

## Sources

Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12; Montgomery–Vaughan, *Multiplicative
Number Theory I*, Lemma 5.1, Theorem 5.2 and the proof of Theorem 12.5; Davenport, *Multiplicative
Number Theory*, ch. 17.

## Method

**`perron_single_term`** (`PerronDev.lean`). For `c, T > 0` and `y > 0`, `y ≠ 1`, the bound has
two halves.
- The `1/(πT|log y|)` half moves the contour to a finite rectangle. For `y > 1` it moves left:
  `y^s/s = (y^s − 1)/s + 1/s`, where the first part is entire and the rectangle integral of `1/s`
  is `2πi`. For `y < 1` it moves right. The far side is bounded for each width, so no limits of
  integrals appear.
- The `1` half moves onto the circular arc of radius `|c + iT|`, using a primitive on a disc
  (`DifferentiableOn.isExactOn_ball`).

**`perron_general`** (`PerronGeneral.lean`). On the segment, `LSeries a s · x^s/s` is
`∑ₙ aₙ (x/n)^s / s`. Each term is at most `‖aₙ‖ (x/n)^σ₀ / σ₀`, which is summable because
`abscissaOfAbsConv a < σ₀`. So dominated convergence swaps the sum and the finite integral
(`intervalIntegral.hasSum_integral_of_dominated_convergence`).
- For `n ≠ x`, the single-term bound applies at `y = x/n`.
- For `n = x`, the integral is `2·arg(σ₀ + iT)`, and `π/2 − arg(σ₀ + iT) ≤ σ₀/T`.
- The right-hand series is proved summable, so it is never the junk value `0`.

**`perron_psi`** (`PerronPsi.lean`). Take `aₙ = Λ(n)` and `σ₀ = c = 1 + 1/log x`, so
`x^c = e·x`. The constant is `C = 400`, which is not optimised.
- `n = x`: the term is at most `log x / T`.
- `n ≤ x/2` or `n ≥ 2x`: here `|log(x/n)| ≥ log 2` and `Λ(n) ≤ 2 log x · n^{1/(2 log x)}`. The
  p-series bound `∑ n^{-p} ≤ 1 + 1/(p − 1)` sums these terms to `O(x log²x / T)`.
- `x/2 < n < 2x`, `n ≠ x`: here `|log(x/n)| ≥ |x − n|/(2x)`, so each term is at most
  `16 log x · min(1, x/(T|x − n|))`.
  - At most two prime powers lie within 1 of `x`. Each is at distance at least `⟨x⟩`, and
    `⟨x⟩ > 0` is proved, so these give the `log x · min(1, x/(T⟨x⟩))` term.
  - The remaining terms form a harmonic sum of size `O(x log²x / T)`.

## Files

- `PerronDev.lean`: the single-term bound, namespace `TruncPerron` (about 640 lines). The
  definitions of `HIntegral`, `VIntegral`, `RectangleIntegral` and the rectangle integral of `1/s`
  are adapted from PrimeNumberTheoremAnd, `ResidueCalcOnRectangles.lean` (Apache-2.0).
- `PerronGeneral.lean`: `perron_general` from `perron_single_term`, namespace
  `TruncPerronGeneral` (about 230 lines).
- `PerronPsi.lean`: `perron_psi` from `perron_general`, namespace `TruncPerronPsi` (about 540
  lines).
- `Solution.lean`: the three `challenge_*` theorems.

## Building

```bash
lake build                  # from this directory
```

A cold build takes about ten minutes, most of it Mathlib.
