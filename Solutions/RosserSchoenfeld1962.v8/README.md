# Rosser–Schoenfeld 1962, equation (3.19)

Proves `log log x < ∑_{p ≤ x} 1/p` for every real `x > 1`: equation (3.19), the Corollary to
Theorem 5 of Rosser and Schoenfeld (1962). The [core conclusion](../../IEANTN/Nodes/RosserSchoenfeld1962/v8/Conclusions.lean)
imports Mathlib only. [Solution.lean](Solution.lean) holds the single Comparator-facing theorem
and imports the conclusion and the proof, never the generated challenge.

## Proof

[RSPrimeRecip.lean](RSPrimeRecip.lean), about 290 lines. The argument is elementary and does not
follow the paper, which derives (3.19) from Theorem 5 and prime tables.

1. Legendre's bound `v_p(N!) ≤ N/(p-1)` (Mathlib's `Nat.factorization_factorial_le_div_pred`)
   and `N^N/N! ≤ e^N` give `S(N) := ∑_{p ≤ N} log p/(p-1) ≥ log N - 1` for all `N ≥ 1`.
2. Discrete partial summation: with `Q(N) := ∑_{p ≤ N} 1/(p-1)`,
   `Q(N) - S(N)/log N - (1 + 1/T)/log N - log log N` is nondecreasing for `N ≥ T`.
3. `∑ 1/p = Q - ∑ 1/(p(p-1))`, and `∑_{p ≤ N} 1/(p(p-1)) ≤ ∑_{p ≤ 13} 1/(p(p-1)) + 1/13`.
4. One numerical inequality at `T = 30` (margin about 0.05) covers `x ≥ 30`; the 28 cases
   `2 ≤ ⌊x⌋ ≤ 29` are checked directly; `⌊x⌋ = 1` is `log x < log 2 < 1`.

All numerics use LeanCert's `interval_decide (trust := kernel)`. The tactic's default mode goes
through `native_decide`, which Comparator does not permit, so kernel mode is used throughout.
No numerical fact is assumed.

## Dependencies and build

The core toolchain and Mathlib pins are inherited from `../..`. LeanCert is a solution-only
dependency pinned to `0a47d99fdd1e61e8eeb96a162343f36bc01e1f92` (LeanCert's `v4.34.0` tag). The
pin used by `RosserSchoenfeld1962.v1` (`6b11513`) was tried first: `LeanCert.Tactic.IntervalAuto`
reaches `LeanCert.Core.Dyadic` and
`LeanCert.Engine.TaylorModel.Hyperbolic`, which fail to elaborate against the core's Mathlib at
that pin.

```bash
lake build
lake --dir Solutions/RosserSchoenfeld1962.v8 build
```

## Provenance

Written by Devon Wright with Grok Bot, first against PNT+ (Lean v4.35.0) as a proof of
`RS_prime.theorem_c` (PrimeNumberTheoremAnd issue #1694), then moved here unchanged apart from
the header and docstrings. It was never merged into PNT+. No mathematical novelty is claimed;
the result is Rosser and Schoenfeld's.
