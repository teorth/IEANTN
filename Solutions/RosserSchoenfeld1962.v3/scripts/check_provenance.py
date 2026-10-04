#!/usr/bin/env python3
# Authors: Håkon Xue-Lønmo
"""Check reused v1 sources without requiring unpublished Git objects or workspaces.

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
    sources = provenance["reused_sources"]
    actual = {
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "Solutions/RosserSchoenfeld1962.v1/RS12").glob("*.lean")
    }
    if actual != set(sources):
        raise SystemExit("The RS12 source inventory has changed")
    for name, digest in sources.items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"Reused source differs: {name}")
        if args.canonical:
            blob = subprocess.check_output(
                ["git", "show", f"{provenance['reused_source_commit']}:{name}"], cwd=ROOT
            )
            if hashlib.sha256(blob).hexdigest() != digest:
                raise SystemExit(f"Canonical source differs: {name}")
    print(f"All {len(sources)} reused v1 sources match the recorded SHA-256 inventory.")
    if args.canonical:
        print(f"Canonical public v1 merge: {provenance['reused_source_commit']}")


if __name__ == "__main__":
    main()
