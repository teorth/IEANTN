#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Håkon Xue-Lønmo
"""Compile local modules in import order with one certificate compiler at a time."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parent.parent
seen = set()
order = []

def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = root / (module.replace('.', '/') + '.lean')
    assert source.is_file(), source
    for dep in re.findall(r'^import (\S+)', source.read_text(), re.M):
        if dep.startswith('Max113.'):
            visit(dep)
    order.append(module)

visit('Solution')
for module in order:
    subprocess.run(['lake', 'build', module], cwd=root, check=True)
