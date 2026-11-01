#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Håkon Xue-Lønmo
"""Compare full challenge/solution types and audit axioms in separate Lean environments."""
from pathlib import Path
import json
import re
import subprocess

root = Path(__file__).resolve().parent.parent
config = json.loads((root / 'comparator.json').read_text())
out = root / '.lake' / 'audit'
out.mkdir(parents=True, exist_ok=True)
names = config['theorem_names']


def run(label, module, commands):
    source = out / f'{label}.lean'
    options = 'set_option pp.all true\n' if label != 'axioms' else ''
    source.write_text(f'import {module}\n' + options + commands)
    result = subprocess.run(['lake', 'env', 'lean', str(source)], cwd=root,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / f'{label}.out').write_text(result.stdout)
    if result.returncode:
        raise SystemExit(result.stdout)
    return result.stdout


checks = ''.join(f'#check @{name}\n' for name in names)
challenge = run('challenge', config['challenge_module'], checks)
solution = run('solution', config['solution_module'], checks)
if challenge != solution:
    raise SystemExit(f'Challenge and solution types differ; inspect {out}')
axioms = run('axioms', config['solution_module'],
             ''.join(f'#print axioms {name}\n' for name in names))
matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axioms)
if {name for name, _ in matches} != set(names) or len(matches) != len(names):
    raise SystemExit(f'Unexpected axiom output:\n{axioms}')
allowed = set(config['permitted_axioms'])
for name, printed in matches:
    found = {axiom.strip() for axiom in printed.split(',') if axiom.strip()}
    if found != allowed:
        raise SystemExit(f'{name}: expected exactly {sorted(allowed)}, got {sorted(found)}')
print(f'PASS: {len(names)} identical pp.all types; exactly the three permitted axioms')
print(axioms, end='')
