#!/usr/bin/env python3
"""Compare the 35 ported certificate modules with git blobs at the validated PNT+ pin.

This reads the upstream repository without checking out, building, or modifying it.
It checks source correspondence, not theorem validity; the Lean build checks the latter.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PIN = "81eca5aa3fa4779883a9aeba18e49087c5366e0f"
HEADER = """/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
"""


def adapted_certificate(original: str) -> str:
    """Only metadata, the license header, and relocated import names may differ."""
    body = re.sub(r"^@\[blueprint\b.*?\]\n", "", original, flags=re.M | re.S)
    body = body.replace("PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RS12.", "RS12.")
    return HEADER + body


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="Read-only PNT+ git repository")
    args = parser.parse_args()
    provenance = json.loads((ROOT / "provenance.json").read_text())
    if provenance["source_commit"] != PIN:
        raise SystemExit("The provenance pin does not match the validated source commit")
    generated = {
        *(f"FactorialData{i:02d}" for i in range(12)),
        *(f"PsiData{i:02d}" for i in range(20)),
        "FactorialData", "PsiFiniteBase", "PsiFinite",
    }
    checked: set[str] = set()
    for record in provenance["files"]:
        name = Path(record["target"]).stem
        if name not in generated:
            continue
        original = subprocess.check_output(
            ["git", "-C", str(args.upstream), "show", f"{PIN}:{record['source']}"]
        )
        if hashlib.sha256(original).hexdigest() != record["source_sha256"]:
            raise SystemExit(f"Source hash mismatch: {record['source']}")
        expected = adapted_certificate(original.decode()).encode()
        if (ROOT / record["target"]).read_bytes() != expected:
            raise SystemExit(f"Certificate differs beyond the documented port: {record['target']}")
        checked.add(name)
    if checked != generated:
        raise SystemExit(f"Certificate inventory mismatch: {sorted(generated - checked)}")
    print(f"All {len(checked)} certificate modules match PNT+ at {PIN} after relocation.")


if __name__ == "__main__":
    main()
