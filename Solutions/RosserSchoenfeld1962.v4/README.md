# Rosser–Schoenfeld 1962: Theorem 13: maximum at 361 and equation (3.36)

This separate solution ports the completed PNT+ historical proof. The core conclusions use
Mathlib only. The adapter imports the conclusions and the local proof, never the Challenge.
Each adapter takes `RosserSchoenfeld1962.v1.equation_3_35` explicitly.
No v1 proof source is imported or compiled, and no sibling `srcDir` remains.
The local logarithm enclosures still require LeanCert at
`6b11513512c9d27183fb4725bfc291ab38b4a6d7`, alongside Mathlib and the IEANTN core path dependency.

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

The sequential builder limits concurrent certificate compilation. With caches populated,
`lake build` suffices. Comparator configuration includes every conclusion and enables NanoDa.
Official verification is a separate maintainer workflow; no receipt is supplied by the author.
No mathematical novelty is claimed.

## Proof route and local audit

Use the supplied equation (3.35). Keep only the pointwise prime-power majorant from PrimePowers. Above 46656 derive the strict 7/5 square-root bound. Below that threshold reduce to the 83 proper prime-power jumps, verify rational Taylor logarithm enclosures and integer square inequalities, then compare the exact anchor at 361 with the strict decimal 1.42620. No uniqueness conclusion is exported.

The core and solution builds passed. Every compared theorem has an identical
`pp.all` type to its generated challenge and exactly `propext`, `Classical.choice`,
and `Quot.sound`; `ieantn.py progress --write` reports zero holes. Reproduce the
type and axiom audit with `python3 scripts/audit.py` after building.

The node now designates the existing `rs1962-paper` literature justification.
The obsolete `lean-noncompliant` entry and its issue #164 blocker have been removed
for this node; they describe the original port's resolved metadata history.
The local proof and validation records above are preserved. Official Comparator
verification and its workflow-generated receipt remain pending.

Both conclusions depend on equation (3.35): `psi_sub_theta_le_prime_powers`
uses it at the square, cube, and fifth roots; `gap_large` uses that bound;
`theorem13_maximum` uses `gap_large` above 46656; and `theorem13_bound`
derives (3.36) from that maximum and the independent anchor bound at 361.
The finite jump checks and anchor calculation need no v1 hypothesis.
