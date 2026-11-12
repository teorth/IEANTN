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

## Explain why a theorem is conditional

`scripts/evidence_queries.py` reads an export and does not write the repository:

```sh
python scripts/ieantn.py export > current.json
python scripts/evidence_queries.py --input current.json explain FKS2.v1.corollary_14
```

`explain` returns one shortest witness path to each unproved leaf, with the
evidence label, receipt and source at each step. A multi-premise bridge stays
conjunctive: the path is a witness, and every listed premise is still required.
A cited intermediate statement is itself an unproved leaf in addition to any
assumptions below it. This is a record of dependencies, not a probability.

## Compare a recorded spare justification

`compare --justification ID` copies the export, selects one recorded spare, and
reports leaves gained or discharged for the conclusion and its downstream
consumers. It does not designate that spare, invent a trust score, or write
metadata. A spare Lean route with no receipt assessment stays an unproved leaf.
Cycles and unknown premises are errors.

## Transitive impact

`impact --base before.json` compares two exports. It names statement,
requirement, designation and receipt-health changes, a witness path to each
downstream consumer, and repair advice derived from that change. `ieantn.py
diff` remains the enforcement gate. Advice does not claim a proposed bridge
has been proved.

## Budgeted re-verification plan

`refresh-plan` groups stale or broken conclusions by node, ranks broken
evidence ahead of environmental staleness, then by downstream reach. Costs are
optional estimates in seconds. An unknown cost never counts as zero inside a
finite budget. The plan does not dispatch a run.
