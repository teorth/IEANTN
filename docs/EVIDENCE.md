# Evidence JSON interface

`python scripts/ieantn.py export > evidence.json` emits a deterministic, versioned
projection of the active graph. Add `--include-inactive` to inspect retained
inactive nodes too. It reads committed metadata, fingerprints and receipts;
it does not build Lean, verify receipts online, dispatch jobs or modify files.

The top-level object has `schema_version: 1`, `environment`,
`includes_inactive`, `nodes` and `conclusions`. Lists are sorted by stable
identifiers; there is no wall-clock timestamp or machine-specific absolute path.
The schema is [evidence-v1.schema.json](evidence-v1.schema.json).

Each conclusion records its declaration, challenge, source/metadata paths,
fingerprint, import completeness, designated justification, every recorded spare,
effective evidence label, receipt health and unproved leaves. Receipt health
uses the existing view assessment: environment staleness and statement drift
remain different. A run URL is evidence metadata, not a fresh online
authentication of that run. A missing fingerprint is null, not a fabricated hash.

`requirements` contains the premises of the designated route. All listed
premises are needed **together**. An import has `relation: "import"`; a
designated bridge source has `relation: "bridge"`. Alternate justifications
are recorded under `justifications` and do not add requirements until designated.
An unproved claim can be a leaf while also having upstream requirements: the
claim itself has not been proved from those requirements.

Example consumer:

```python
import json
import sys

document = json.load(sys.stdin)
if document["schema_version"] != 1:
    raise SystemExit("unsupported evidence schema")
for conclusion in document["conclusions"]:
    if conclusion["unproved_leaves"]:
        print(conclusion["key"], conclusion["unproved_leaves"])
```

Invalid graph metadata causes failure with diagnostics on stderr and no partial
JSON on stdout. Consumers should reject unsupported schema versions. These
fields describe recorded evidence, not a probability of correctness, source
alignment certification or a claim that an inactive result is in the core build.

## Explain, compare, inspect impact and plan refreshes

The companion `scripts/evidence_queries.py` consumes this interface without
access to the repository. Every query writes JSON and leaves the input untouched:

```sh
python scripts/ieantn.py export > current.json
python scripts/evidence_queries.py --input current.json explain FKS2.v1.corollary_14
python scripts/evidence_queries.py --input current.json compare Lcm.v1.lcmUpto_not_highlyAbundant --justification bridge-from-v2
python scripts/evidence_queries.py --input current.json impact --base before.json
python scripts/evidence_queries.py --input current.json refresh-plan --costs costs.json --budget 3600
```

`explain` returns one shortest witness path to each unproved leaf and lists
reachable claims whose imports are incompletely traced. Paths explain why a
premise enters; siblings remain conjunctive even when the witness follows only
one branch. A cited intermediate statement is itself an unproved leaf in
addition to any assumptions below it.

`compare` selects a recorded spare only in a copied snapshot and reports
gained/discharged leaves for every affected consumer. It refuses cycles and
unknown premises. A spare Lean route whose receipt is not assessed by the
export remains an unassessed leaf, rather than inheriting a green label.
No numerical trust score is computed and no designation is written.

`impact` compares two exported snapshots, reporting statement fingerprints,
requirements, designation and receipt-health changes. It identifies transitive
consumers with concrete witness paths and review/repair advice. This extends
inspection; the existing `ieantn.py diff` remains the enforcement gate. The
query does not claim that a suggested new bridge has been proved.

`refresh-plan` deduplicates runs at node granularity and ranks broken evidence
ahead of environmental staleness, then by downstream reach. `costs.json` maps
node IDs to positive finite seconds, for example `{"Lcm.v1": 90}`. Costs are
planning estimates, not authenticated run facts. With a finite budget, unknown
costs remain queued and cannot silently consume zero seconds. Every proposed
run names all the node's conclusions, since official verification is per node.
This command never dispatches runs.

Unknown schemas, duplicate JSON keys, dangling references, unsupported evidence
shapes and cycles are errors. The queries use iterative graph traversal, so a
valid long chain does not depend on Python's recursion limit.


