# Rosser–Schoenfeld 1962, equation (3.9)

The solution proves both strict inequalities for every real x > 1.
It has no logical dependency on another IEANTN node.

Positivity applies Mathlib’s Bertrand theorem at floor(x). For the upper
bound, the product of primes in (n,2n] divides the central binomial
coefficient, which is bounded by 2^(2n). Taking logarithms gives
θ(2n) ≤ θ(n) + 2n log 2. The real-variable bridge at n = floor(x)+1 yields

    (π(2x) − π(x)) log x ≤ θ(2x) − θ(x)
      ≤ 2(x+1) log 2 + log(x+1).

For x ≥ 1024 this is strictly less than (7/5)x, using Mathlib’s certified
bound on log 2 and log t ≤ t−1. The proof establishes log x > 0 before division.
For 1 < x < 2, π(2x) ≤ 2 suffices. For 2 ≤ x < 1024, put n = floor(x)
and k = floor(log₂(n+1))+1. The kernel-checked inequality

    (π(2n+1) − π(n)) k ≤ 2n

combines with log x < (7/10)k. The integer range 2 ≤ n ≤ 1023 is covered
by 27 monotonicity blocks in three sequentially dependent modules.
Each count uses Mathlib’s binary `Num.Prime` instance and `decide +kernel`.
`fastCount_eq` and `range_bound` prove the computation and block reduction
sound. There are no unverified numerical assumptions or external certificates.

The paper derives the corollary from its analytic estimates, checking uncovered
ranges in prime tables; it identifies Bertrand and Finsler as the sources of the
two sides (p. 69). This is the same historical statement with a different formal
proof. No mathematical novelty is claimed.

## Provenance and reproduction

The new proofs and integration are by Håkon Xue-Lønmo, developed with OpenAI
Codex. Mathlib is pinned to `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` in
both manifests. Imported infrastructure includes `NumberTheory/Bertrand.lean`,
`NumberTheory/Primorial.lean`, `NumberTheory/Chebyshev.lean`, `Data/Num/Prime.lean`,
and `Analysis/Complex/ExponentialBounds.lean`; no Mathlib source is copied.
Repository: https://github.com/leanprover-community/mathlib4.

The interval-counting argument adapts the real prime-set and sum-difference
method reviewed in the v3 source, reversing its log bound:

- repository: https://github.com/teorth/IEANTN (public PR #188)
- commit: `bbe36b1d5c5b8b5b7fdbf3dbee0f6e9f06fb9bd3`
- path: `Solutions/RosserSchoenfeld1962.v3/Interval/Counting.lean`
- SHA-256: `ac2daae0ea04e36cd6a518408664c00d1d932b09a7f1d3e646c0ed1d0648819f`
- adaptation: a lower bound on the theta difference by count times log x,
  directly using Mathlib’s sets rather than carrying the v3 helper definitions.

This is source reuse only: v3 is neither a logical dependency nor a Git ancestor.
The candidate is based on upstream main `ef21db9ba5dceffd976da71e24f8497b3a13f798`.
There is no PNT+ source dependency and no unpublished source object is needed.

Run `python3 generate.py --check`, then `lake build` in this directory.
The three generated modules form an import chain to keep certificate compilation
sequential. Run the root `ieantn.py progress`, `gen-challenges --check`,
`fingerprint --check`, and `check` commands for this node.
The generator selects blocks; Lean independently checks all numbers.
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
Official Comparator verification remains pending; no receipt is authored here.
