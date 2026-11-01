# Rosser–Schoenfeld 1962: equation (5.4)

This separate solution ports the completed PNT+ historical proof. The core conclusions use
Mathlib only. The adapter imports the conclusions and the local proof, never the Challenge.
The unchanged v1 RS12 proof library is reused through a sibling `srcDir`; its outputs belong
to this solution. No IEANTN node conclusion is assumed. LeanCert uses the same pinned commit
as v1 and remains a solution-only dependency.

The source was a read-only working-tree snapshot based at `81eca5aa3fa4779883a9aeba18e49087c5366e0f`. That commit alone does
not identify the new files. `provenance.json` pins each source and ported file by SHA-256,
and inventories all unchanged inherited RS12 sources. It is not a verification receipt.
`progress.yaml` records the statement audit, dependency pruning, and local validation.

From this solution directory:

```sh
lake update
python3 scripts/check_port.py
# Optional comparison against the original read-only working-tree snapshot:
python3 scripts/check_port.py --source /home/hxl/src/PNT-current
python3 scripts/build_sequential.py
```

The sequential builder limits concurrent certificate compilation. With caches populated,
`lake build` suffices. Comparator configuration includes every conclusion and enables NanoDa.
Official verification is a separate maintainer workflow; no receipt is supplied by the author.
No mathematical novelty is claimed.

## Proof route and local audit

Reuse theta_le_psi and the actual v1 RS12 proof, comparing the exact coefficients 1.03883 < 1.11 for x > 0. This is the completed PNT+ proof, rather than the historical route through Theorems 25 and 18.

The core and solution builds passed. Every compared theorem has an identical
`pp.all` type to its generated challenge and exactly `propext`, `Classical.choice`,
and `Quot.sound`; `ieantn.py progress --write` reports zero holes. Reproduce the
type and axiom audit with `python3 scripts/audit.py` after building.

The current upstream verification boundary is tracked in
[issue #164](https://github.com/teorth/IEANTN/issues/164): admitting the pinned
LeanCert dependency and arranging certificate compilation within runner memory.
These local checks do not resolve that policy question or create a receipt.
