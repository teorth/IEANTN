#!/usr/bin/env python3
"""Check every optional source dossier. A node without one is fine.

    python3 scripts/check_dossiers.py

This does not claim that a declaration matches its paper. It checks that a dossier which is
present names an edition and a locator and that each displayed numeral sits on the side of its
exact rational that the rounding direction requires. See docs/DOSSIERS.md.
"""

from __future__ import annotations

import pathlib
import sys

import yaml

from dossiers import validate_dossier

ROOT = pathlib.Path(__file__).resolve().parent.parent
NODES_DIR = ROOT / "IEANTN" / "Nodes"


def node_id(directory: pathlib.Path) -> str:
    """`IEANTN/Nodes/Lcm/v1` -> `Lcm.v1`."""
    return directory.relative_to(NODES_DIR).as_posix().replace("/", ".")


def main() -> int:
    paths = sorted(NODES_DIR.rglob("dossier.yaml"))
    if not paths:
        print("no source dossiers; nothing to validate")
        return 0
    failed = 0
    for path in paths:
        directory = path.parent
        try:
            data = yaml.safe_load(path.read_text(encoding="utf-8"))
        except yaml.YAMLError as error:
            failed += 1
            print(f"{path.relative_to(ROOT)}: {error}")
            continue
        errors = validate_dossier(data, node_id(directory))
        if errors:
            failed += 1
            print(f"{path.relative_to(ROOT)}:")
            for error in errors:
                print(f"  {error}")
    print(f"validated {len(paths) - failed} of {len(paths)} source dossier(s)")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
