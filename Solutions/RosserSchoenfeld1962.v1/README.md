# Rosser–Schoenfeld 1962, equation (3.35)

This solution ports the proved theorem `RS_prime.theorem_12` from PNT+ commit
[`81eca5aa3fa4779883a9aeba18e49087c5366e0f`](https://github.com/hakonlonmo/PrimeNumberTheoremAnd/tree/81eca5aa3fa4779883a9aeba18e49087c5366e0f).
It proves `ψ(x) < 1.03883 x` for every positive real `x`, equation (3.35) in
Rosser and Schoenfeld's 1962 Theorem 12. The theorem's additional assertion that
`ψ(x) / x` attains its maximum at `x = 113` is outside this port's scope.

The [core conclusion](../../IEANTN/Nodes/RosserSchoenfeld1962/v1/Conclusions.lean)
uses Mathlib's `Chebyshev.psi`, including the integer endpoint. It has no
solution dependencies. [Solution.lean](Solution.lean) supplies the single
Comparator-facing theorem `RosserSchoenfeld1962.v1.challenge_equation_3_35`.
It imports the conclusion and the local proof, never the generated challenge.

## Proof and provenance

[progress.yaml](progress.yaml) records the source audit, transitive import
closure, dependency choices, adaptations, and validation status.
[provenance.json](provenance.json) records the pinned source paths and hashes.
The `RS12/` modules preserve the upstream proof boundaries and mathematical
content. Broad analytic imports were replaced by the eight needed Chebyshev
declarations and one finite-set identity; LeanArchitect annotations were removed.
The upstream theorem name `RS_prime.theorem_12` is retained.

The finite certificate still covers `500000`. The large-range argument still
uses `ψ(x) ≤ 1.021*x + ψ(x/60)` and strong induction. The 35 generated certificate
modules are local to this solution: `FactorialData00`–`FactorialData11`,
`FactorialData`, `PsiData00`–`PsiData19`, `PsiFiniteBase`, and `PsiFinite`.
Their values, checker logic, and kernel computations are preserved. No later
cutoff experiments are included. No numerical assertions are assumed as axioms.

To compare these certificates with the source without modifying the source:

```bash
python3 Solutions/RosserSchoenfeld1962.v1/scripts/check_certificates.py ~/src/PNT-current
```

## Dependencies and build

Like the other IEANTN solutions, this project takes IEANTN from `../..` and
uses the core toolchain, Mathlib, and support-package revisions. LeanCert is a
solution-only dependency pinned to the exact upstream commit
`6b11513512c9d27183fb4725bfc291ab38b4a6d7`. The IEANTN requirement comes last so
that its dependency pins take precedence in Lake's resolution. Neither the
PNT+ project nor its toolchain is needed to build this port.

From the IEANTN root, with the repository's Python requirements installed:

```bash
lake build
lake --dir Solutions/RosserSchoenfeld1962.v1 update
python3 Solutions/RosserSchoenfeld1962.v1/scripts/build_sequential.py
python3 scripts/ieantn.py progress RosserSchoenfeld1962.v1 --write
```

The certificate shards are memory intensive. The sequential helper builds the
local import closure one module at a time using ordinary `lake build` commands,
then runs the default solution build. It uses Lake's incremental caches and
writes diagnostic logs under the ignored `.lake/rs12-build-logs/` directory.
Once the shards are cached, the usual command is sufficient:

```bash
lake --dir Solutions/RosserSchoenfeld1962.v1 build
```

## Verification boundary

Local build, type, and axiom checks are recorded in `progress.yaml`. They do not
produce an IEANTN verification receipt. Maintainer-side Comparator verification,
including the configured second kernel, remains a separate workflow step.
Only that workflow may create the receipt and designate a Lean justification.

The original mathematics is due to Rosser and Schoenfeld; this port claims no
novel result. The upstream formalization and this adaptation used substantial
OpenAI assistance under human direction, documented in the node metadata.
