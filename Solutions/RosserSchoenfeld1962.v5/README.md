# Rosser–Schoenfeld 1962: equation (5.4)

This separate solution ports the completed PNT+ historical proof. The core conclusions use
Mathlib only. The adapter imports the conclusions and the local proof, never the Challenge.
The adapter takes `RosserSchoenfeld1962.v1.equation_3_35` as an explicit hypothesis.
The proof uses Mathlib's `theta_le_psi` and the exact comparison `1.03883 < 1.11`.
No v1 proof source is compiled; the only proof dependency is Mathlib, supplied by the
IEANTN core path dependency.

The source was a read-only working-tree snapshot based at `81eca5aa3fa4779883a9aeba18e49087c5366e0f`. That commit alone does
not identify the new files. `provenance.json` pins each source and ported file by SHA-256,
and retains the original RS12 inventory for historical attribution only. It is not a verification receipt.
`progress.yaml` records the statement audit, dependency pruning, and local validation.

From this solution directory:

```sh
lake update
python3 scripts/check_port.py
# Optional comparison against the original read-only working-tree snapshot:
python3 scripts/check_port.py --source /path/to/PNT-checkout
python3 scripts/build_sequential.py
```

`lake build` builds this small Mathlib-only solution. The sequential builder also works. Comparator configuration includes every conclusion and enables NanoDa.
Official verification is a separate maintainer workflow; no receipt is supplied by the author.
No mathematical novelty is claimed.

## Proof route and local audit

Apply `theta_le_psi`, the supplied equation (3.35), and the exact coefficient comparison.

The core and solution builds passed. Every compared theorem has an identical
`pp.all` type to its generated challenge and exactly `propext`, `Classical.choice`,
and `Quot.sound`; `ieantn.py progress --write` reports zero holes. Reproduce the
type and axiom audit with `python3 scripts/audit.py` after building.

The node now designates the existing `rs1962-paper` literature justification.
The obsolete `lean-noncompliant` entry and its issue #164 blocker have been removed
for this node; they describe the original port's resolved metadata history.
The local proof and validation records above are preserved. Official Comparator
verification and its workflow-generated receipt remain pending.