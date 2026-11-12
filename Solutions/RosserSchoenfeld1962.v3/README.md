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

`Solution.lean` proves `RosserSchoenfeld1962.v3.challenge_equation_3_8` from the explicit
`RosserSchoenfeld1962.v1.equation_3_35` hypothesis. The formal proof uses a different route from
the paper's Theorem 2 estimates and finite prime tables. No mathematical novelty
is claimed from this difference.

* `Interval/Lower.lean` adapts elementary weighted-factorial support from PNT+
  to prove `ψ(y) ≥ 0.92*y - 5*log(y) - 1` for `y ≥ 30`.
* `Interval/Counting.lean` relates the cardinality and θ sum of `(x, 2x]`.
* `Interval/Tail.lean` combines the lower bound, Mathlib's Costa–Pereira
  inequality, and the supplied equation (3.35), `ψ(x) < 1.03883*x`, for `x ≥ 4096`.
  Its docstring and `progress.yaml` describe the cutoff and numerical margins.
* `Interval/FiniteCheck.lean` proves the soundness of primality, ordering,
  endpoint and logarithm checks. `Data000` through `Data047` supply 3,356 prime
  witnesses covering `[41/2, 4096)`. Primality checks use `decide +kernel` in
  batches of at most 64. `Interval/Finite.lean` assembles the 48 intervals.
* `Interval/Dyadic.lean` retains a secondary specialization to dyadic intervals,
  conditional on the new conclusion. It is not needed by the principal theorem.

The solution imports v1's Conclusions module only. `RSInterval.tail` takes its
equation (3.35) as an explicit hypothesis; no v1 proof source is compiled.
`Interval/FactorialSupport.lean` contains only the elementary identities needed
by `Interval/Lower.lean`, with a Mathlib interval lemma replacing the custom one.
No v2 fact is used and no sibling `srcDir` remains.

`provenance.json` retains the original v1 inventory as historical attribution,
and pins the extracted support and adapted files separately. The weighted-factorial source is at public
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

The sequential runner bounds memory use for this solution's own certificates and
finishes with an ordinary `lake build`. The generator supplies data only; Lean
checks every property. `check_provenance.py --canonical` additionally compares
the extracted support's source against the public v1 merge in a full Git clone.

The saved `.lake/audit/challenge.out` and `solution.out` have identical full types;
`axioms.out` lists exactly `propext`, `Classical.choice`, and `Quot.sound`.
These existing results were read during the metadata review, without rerunning Lean.
The node retains its `rs1962-paper` literature designation, its declared v1 input,
and its necessary pinned LeanCert dependency. Official Comparator verification
and its workflow-generated receipt remain pending.

## Relation to equation (3.9)

[PR #192](https://github.com/teorth/IEANTN/pull/192) proves
`0 < pi(2*x)-pi(x) < 7*x/(5*log x)` for `x > 1`; see its
[`Solution.lean`](https://github.com/hakonlonmo/IEANTN/blob/rosser-schoenfeld-1962-eq39-pr/Solutions/RosserSchoenfeld1962.v7/Solution.lean).
Its Bertrand positivity and binomial upper bound do not prove this quantitative
lower bound. An adaptation would need a lower estimate for the prime count or
theta difference strong enough to exceed `3*x*log(2*x)/(5*log x)`, together with
the remaining finite range. Here `RSInterval.tail` supplies such a theta lower
estimate from the weighted-factorial bound, Costa–Pereira, and the v1 hypothesis.

The v7 README records adaptation of this project's `Interval/Counting.lean`:
`theta_sub_le` bounds each summand by `log(2*x)` for a lower count bound;
v7's `RS39.count_mul_log_le` bounds it below by `log x` for an upper count bound.
There is source-level reuse of that technique, but no shared local proof module
or cross-import between the two projects. Their certificates and tail arguments
are distinct. The recorded history establishes this adaptation, not intentional
independence or supersession; the two outward-facing results remain separate.

Run `python3 scripts/audit.py` after building to compare every listed theorem
with its generated challenge in separate Lean environments, check the three
permitted axioms, and inspect the actual loaded import closure. These local
checks passed; they are not an official Comparator or NanoDa result.
`comparator.json` enables the NanoDa replay required by the official workflow.
