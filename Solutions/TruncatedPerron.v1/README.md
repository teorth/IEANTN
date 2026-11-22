# TruncatedPerron.v1: the truncated Perron formula

This proves all three conclusions of `TruncatedPerron.v1` exactly as the challenge states them, no
`sorry`:

```lean
theorem TruncatedPerron.v1.challenge_perron_single_term : TruncatedPerron.v1.perron_single_term
theorem TruncatedPerron.v1.challenge_perron_general : TruncatedPerron.v1.perron_general
theorem TruncatedPerron.v1.challenge_perron_psi : TruncatedPerron.v1.perron_psi
```

`#print axioms` on each gives `[propext, Classical.choice, Quot.sound]`. The node doesn't import
any other node, so these are unconditional.

Each conclusion is proved from the one before it: `perron_general` uses `perron_single_term`, and
`perron_psi` uses `perron_general`.

## Sources

Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12; Montgomery–Vaughan, *Multiplicative
Number Theory I*, Lemma 5.1, Theorem 5.2 and the proof of Theorem 12.5; Davenport, *Multiplicative
Number Theory*, ch. 17.

## How it goes

**`perron_single_term`** (`PerronDev.lean`). For `c, T > 0` and `y > 0`, `y ≠ 1`, the bound has
two halves.
- For the `1/(πT|log y|)` half, I move the contour to a finite rectangle.
  - For `y > 1` it goes left: `y^s/s = (y^s − 1)/s + 1/s`, the first part is entire, and the
    rectangle integral of `1/s` is `2πi`.
  - For `y < 1` it goes right.
  - The far side is bounded for each width, so there are no limits of integrals.
- For the `1` half, I move onto the circular arc of radius `|c + iT|`, using a primitive on a disc
  (`DifferentiableOn.isExactOn_ball`).

**`perron_general`** (`PerronGeneral.lean`). On the segment, `LSeries a s · x^s/s` is
`∑ₙ aₙ (x/n)^s / s`. Each term is at most `‖aₙ‖ (x/n)^σ₀ / σ₀`, which is summable because
`abscissaOfAbsConv a < σ₀`. That's enough for dominated convergence to swap the sum and the finite
integral (`intervalIntegral.hasSum_integral_of_dominated_convergence`).
- For `n ≠ x`, the single-term bound applies at `y = x/n`.
- For `n = x`, the integral is `2·arg(σ₀ + iT)`, and `π/2 − arg(σ₀ + iT) ≤ σ₀/T`.
- I also prove the right-hand series is summable, so it's never the junk value `0`.

**`perron_psi`** (`PerronPsi.lean`). I take `aₙ = Λ(n)` and `σ₀ = c = 1 + 1/log x`, so
`x^c = e·x`. The constant is `C = 400`; I didn't try to optimise it.
- `n = x`: the term is at most `log x / T`.
- `n ≤ x/2` or `n ≥ 2x`: here `|log(x/n)| ≥ log 2` and `Λ(n) ≤ 2 log x · n^{1/(2 log x)}`. A
  p-series bound, `∑ n^{-p} ≤ 1 + 1/(p − 1)`, sums these terms to `O(x log²x / T)`.
- `x/2 < n < 2x`, `n ≠ x`: here `|log(x/n)| ≥ |x − n|/(2x)`, so each term is at most
  `16 log x · min(1, x/(T|x − n|))`.
  - At most two prime powers are within 1 of `x`. Each is at least `⟨x⟩` away, and I prove
    `⟨x⟩ > 0`, so these give the `log x · min(1, x/(T⟨x⟩))` term.
  - The rest make a harmonic sum of size `O(x log²x / T)`.

## Files

- `PerronDev.lean` (~640 lines): the single-term bound, namespace `TruncPerron`. The definitions
  of `HIntegral`, `VIntegral`, `RectangleIntegral` and the rectangle integral of `1/s` are adapted
  from PrimeNumberTheoremAnd, `ResidueCalcOnRectangles.lean` (Apache-2.0).
- `PerronGeneral.lean` (~230 lines): `perron_general` from `perron_single_term`, namespace
  `TruncPerronGeneral`.
- `PerronPsi.lean` (~540 lines): `perron_psi` from `perron_general`, namespace `TruncPerronPsi`.
- `Solution.lean`: the three `challenge_*` theorems.

## Building

```bash
lake build                  # from this directory
```

A cold build takes about ten minutes, mostly Mathlib.
