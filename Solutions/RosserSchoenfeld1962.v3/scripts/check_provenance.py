#!/usr/bin/env python3
# Authors: Håkon Xue-Lønmo
"""Check local adaptations without requiring sibling proof sources or unpublished objects.

This is a source correspondence check, not a verification receipt. The optional
canonical comparison needs the public v1 merge in a full IEANTN clone.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

SOLUTION = Path(__file__).resolve().parents[1]
ROOT = SOLUTION.parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--canonical", action="store_true")
    args = parser.parse_args()
    provenance = json.loads((SOLUTION / "provenance.json").read_text())
    sources = provenance["local_sources"]
    for name, digest in sources.items():
        if hashlib.sha256((SOLUTION / name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"Local adaptation differs: {name}")
    if args.canonical:
        for item in provenance["adapted_sources"]:
            if "source_commit" not in item:
                continue
            name = item["source"]
            blob = subprocess.check_output(
                ["git", "show", f"{item['source_commit']}:{name}"], cwd=ROOT
            )
            if hashlib.sha256(blob).hexdigest() != item["source_sha256"]:
                raise SystemExit(f"Canonical source differs: {name}")
    print(f"All {len(sources)} local adaptations match their SHA-256 inventory; no sibling sources required.")
    if args.canonical:
        print(f"Canonical public v1 merge: {provenance['reused_source_commit']}")


if __name__ == "__main__":
    main()
