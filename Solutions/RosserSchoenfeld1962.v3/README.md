# Rosser–Schoenfeld 1962, Corollary 3, equation (3.8)

For every real `x ≥ 41/2`,

```text
3*x/(5*Real.log x) < IEANTN.primeCounting (2*x) - IEANTN.primeCounting x.
```

The inequality is strict and counts primes in `(x, 2x]`. This is equation (3.8),
page 69 of Rosser and Schoenfeld, *Approximate formulas for some functions of
prime numbers*, Illinois J. Math. 6 (1962), 64–94
([paper](https://doi.org/10.1215/ijm/1255631807),
[scan](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)).

`Solution.lean` proves `RosserSchoenfeld1962.v3.challenge_equation_3_8` without
hypotheses from other IEANTN nodes. The formal proof uses a different route from
the paper's Theorem 2 estimates and finite prime tables. No mathematical novelty
is claimed from this difference.

* `Interval/Lower.lean` adapts elementary weighted-factorial support from PNT+
  to prove `ψ(y) ≥ 0.92*y - 5*log(y) - 1` for `y ≥ 30`.
* `Interval/Counting.lean` relates the cardinality and θ sum of `(x, 2x]`.
* `Interval/Tail.lean` combines the lower bound, Mathlib's Costa–Pereira
  inequality, and v1's proved equation (3.35), `ψ(x) < 1.03883*x`, for `x ≥ 4096`.
  Its docstring and `progress.yaml` describe the cutoff and numerical margins.
* `Interval/FiniteCheck.lean` proves the soundness of primality, ordering,
  endpoint and logarithm checks. `Data000` through `Data047` supply 3,356 prime
  witnesses covering `[41/2, 4096)`. Primality checks use `decide +kernel` in
  batches of at most 64. `Interval/Finite.lean` assembles the 48 intervals.
* `Interval/Dyadic.lean` retains a secondary specialization to dyadic intervals,
  conditional on the new conclusion. It is not needed by the principal theorem.

The solution has a real **v1 proof dependency and no v2 dependency**. It imports
`RS12.Chebyshev` and `RS12.Proof` from the sibling v1 solution already merged in
[IEANTN #125](https://github.com/teorth/IEANTN/pull/125). In particular,
`RSInterval.tail` uses `RS_prime.theorem_12`; no conclusion is merely assumed,
and no v2 maximum-at-113 fact is used. The custom Lake configuration exposes only
the sibling `RS12` library, so `import Solution` resolves to this v3 adapter.

`provenance.json` records the public v1 merge, SHA-256 hashes of all 51 reused
RS12 sources, and PNT+ adaptations. The weighted-factorial source is at public
PNT+ commit `81eca5aa3fa4779883a9aeba18e49087c5366e0f`. The dyadic adaptation came
from an uncommitted PNT+ workspace file, not that commit; its snapshot hash is
historical attribution only. The adapted proof is included in full and needs no
unpublished object or external workspace. LeanCert is pinned to
`6b11513512c9d27183fb4725bfc291ab38b4a6d7`. Core and solution use the repository's
Lean toolchain. PNT+ contributors retain attribution for adapted proof material;
OpenAI Codex is acknowledged in automation metadata.

From a fresh checkout, build the core with `lake exe cache get` and `lake build`.
Then, from this solution directory:

```sh
lake exe cache get
python3 scripts/check_provenance.py
python3 scripts/generate_finite.py --check
python3 scripts/build_sequential.py
```

The sequential runner bounds memory use for the inherited certificates and
finishes with an ordinary `lake build`. The generator supplies data only; Lean
checks every property. `check_provenance.py --canonical` additionally compares
the inventory against the public v1 merge in a full Git clone.

The intended transitive axiom footprint is at most `propext`, `Classical.choice`
and `Quot.sound`. Local type and axiom checks do not replace the separate
maintainer Comparator workflow. This contribution supplies no receipt and does
not designate `lean-comparator` evidence.
