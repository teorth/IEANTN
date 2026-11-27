# Maximum of ψ(x)/x at 113

Both compared declarations take `RosserSchoenfeld1962.v1.equation_3_35` as a
challenge hypothesis. `tail_strict` applies it at `x/60`, together with the local
weighted-factorial recurrence. The exact maximum stays symbolic. The strict
inequality away from 113, inclusive ψ endpoints, and uniqueness proof are unchanged.
The paper states the maximum; uniqueness is the stronger formal refinement.

The package requires IEANTN (path dependency) and its pinned Mathlib dependencies.
There is no LeanCert requirement, sibling source directory, or import of a v1
solution module. Importing the v1 core Conclusions definition supplies the type of
the declared hypothesis, not a proof of it.

## Local proof support

* `Logs`: twelve-term exponential bounds from the existing Mathlib-only
  `Solutions/Chebyshev.v1/LogBounds.lean` (Terence Tao), six rational logarithm upper
  bounds, and a lower bound at 12774/10000. `Lower` combines that bound with
  Mathlib's `log_two_gt_d9` and the integer LCM comparison at 113.
* `Witness`: only the binary logarithm unit bound, ψ increment identity, factor
  witness soundness, and checker definition needed by `Shifted` and `SmallChecker`.
  The obsolete non-witness checker and its soundness proof are omitted.
* `Small`, `Data00`–`Data19`, `Finite`: the existing small and shifted adapters,
  with local kernel checks of all 1,998 witness blocks. The five-unit seed saving
  remains. `certificates/psi-witnesses.json` contains only integer proposals.
* `Recurrence`: the weighted-factorial identity, integral error bounds, weights,
  periodicity, fixed floor checker and soundness, twelve floor certificate shards,
  slope estimates, upper bound and recurrence. All floor checks are rerun locally.
  The unrelated small-argument factorial lemma and unused list floor checker are
  omitted. No global RS12 theorem, induction, or v1 finite seed is included.

Data and retained recurrence proofs are attributed to Akula and PNT+ contributors,
from IEANTN commit `6664139ccebea21ecdb9bd94539fc75d77564794`.
`certificates/provenance.json` pins each original source hash and the integer data;
`provenance.json` inventories the supplied local support. Generation and checks need
neither a sibling v1 checkout nor its compiled artifacts. These files are source
provenance, not verification receipts.

## Checks

```sh
python3 scripts/generate_adapters.py --check
python3 scripts/check_dependencies.py
python3 scripts/build_sequential.py
python3 scripts/audit.py
```

The final audit needs the generated core Challenge built in the same environment.
See `DEPENDENCIES.md` for the original 46-module audit and the current validation
status. Certificate source availability alone does not establish a completed build.

## Justification and verification status

The published maximum retains its `rs1962-paper` literature designation.
The uniqueness refinement designates `local-proof-awaiting-verification` with
kind `asserted`, recording the author's local proof and validation report in
`DEPENDENCIES.md`. The 1962 paper does not explicitly assert uniqueness.
Both conclusions remain covered by `comparator.json`; official Comparator
verification and its workflow-generated receipt are pending.
