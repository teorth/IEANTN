#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Håkon Xue-Lønmo
"""Check the exact port inventory; optionally compare the read-only PNT+ snapshot."""
from pathlib import Path
import argparse
import hashlib
import json

root = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source', type=Path, help='read-only PNT+ checkout')
args = parser.parse_args()
inventory = json.loads((root / 'provenance.json').read_text())
errors = []

def check(path, expected):
    actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    if actual != expected:
        errors.append(str(path))

for item in inventory['ported']:
    check(root / item['local'], item['local_sha256'])
    if args.source:
        check(args.source / item['source'], item['source_sha256'])
for item in inventory['inherited_rs12']:
    check(root / item['path'], item['sha256'])
if errors:
    raise SystemExit('Source inventory mismatch:\n' + '\n'.join(errors))
print(f"PASS: {len(inventory['ported'])} ported and "
      f"{len(inventory['inherited_rs12'])} unchanged RS12 sources")
