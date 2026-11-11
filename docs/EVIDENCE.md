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

