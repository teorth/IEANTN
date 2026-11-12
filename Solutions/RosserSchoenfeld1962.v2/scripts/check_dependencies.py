#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Håkon Xue-Lønmo
"""Check supplied sources and pinned provenance without any sibling solution."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path(__file__).resolve().parent.parent
inventory = json.loads((root / 'provenance.json').read_text())
actual = {str(p.relative_to(root)) for p in (root / 'Max113').rglob('*.lean')}
actual.add('Solution.lean')
assert actual == set(inventory['local_sources']), 'Source inventory changed'
for name, expected in inventory['local_sources'].items():
    p = root / name
    assert hashlib.sha256(p.read_bytes()).hexdigest() == expected, f'Changed source: {name}'
    s = p.read_text()
    assert 'rs12_private%' not in s, name
    for dep in re.findall(r'^import (\S+)', s, re.M):
        assert dep.startswith(('Max113.', 'Mathlib.', 'IEANTN.Nodes.')), (name, dep)
        assert '.Challenge' not in dep, (name, dep)
        if dep.startswith('IEANTN.'):
            assert dep in {'IEANTN.Nodes.RosserSchoenfeld1962.v1.Conclusions',
                           'IEANTN.Nodes.RosserSchoenfeld1962.v2.Conclusions'}, dep
lake = (root / 'lakefile.lean').read_text()
assert 'srcDir' not in lake and 'leancert' not in lake.lower()
manifest = json.loads((root / 'lake-manifest.json').read_text())
assert all(p['name'].lower() != 'leancert' for p in manifest['packages'])
for name, expected in inventory['support_files'].items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == expected, name
subprocess.run(['python3', str(root / 'scripts/generate_adapters.py'), '--check'], check=True)
print(f'PASS: {len(actual)} local Lean sources; no v1 solution or LeanCert imports')
