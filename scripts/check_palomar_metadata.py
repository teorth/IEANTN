#!/usr/bin/env python3
"""Validate each node's formalization.yaml against Palomar's current submission contract.

Keeping every node continuously Palomar-valid is what makes spinning off a certificate cheap:
the spin-off step becomes "copy the node, generate a self-contained challenge, emit
comparator.json" rather than a metadata rewrite.

The validator is fetched fresh by CI and passed in as a directory; it is deliberately NOT
vendored. Palomar's required-field list moves — `project.description` became mandatory days
after an earlier fetch had accepted a submission without it — so a cached copy would happily
accept files the live contract now rejects.

    python3 scripts/check_palomar_metadata.py /tmp/pal

IEANTN adds `node`, `conclusions` and receipt fields that Palomar does not know about. Those are
stripped before validation; this checks the Palomar-facing subset only.
"""

from __future__ import annotations

import pathlib
import sys
import tempfile

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
NODES_DIR = ROOT / "IEANTN" / "Nodes"

#: Keys that are ours, not Palomar's.
IEANTN_ONLY = ("node", "conclusions")


def main() -> int:
    if len(sys.argv) != 2:
        return int(bool(sys.stderr.write(f"usage: {sys.argv[0]} <validator-dir>\n"))) or 2

    validator_dir = pathlib.Path(sys.argv[1]).resolve()
    sys.path.insert(0, str(validator_dir))
    try:
        from scripts import submission_contract as contract  # type: ignore
    except Exception as error:  # pragma: no cover
        print(f"could not load Palomar's validator from {validator_dir}: {error}")
        return 1

    node_dirs = sorted(d for d in NODES_DIR.iterdir() if (d / "formalization.yaml").is_file())
    failures = 0

    for directory in node_dirs:
        source = directory / "formalization.yaml"
        data = yaml.safe_load(source.read_text(encoding="utf-8")) or {}
        for key in IEANTN_ONLY:
            data.pop(key, None)

        with tempfile.NamedTemporaryFile(
            "w", suffix=".yaml", delete=False, encoding="utf-8"
        ) as handle:
            yaml.safe_dump(data, handle, allow_unicode=True, sort_keys=False)
            staged = pathlib.Path(handle.name)

        try:
            loaded = contract.load_formalization_metadata(staged)
            origin = contract.normalized_provenance(loaded)["result_origin"]
            print(f"ok    {directory.name}  (result_origin: {origin})")
        except Exception as error:
            failures += 1
            print(f"FAIL  {directory.name}: {error}")
        finally:
            staged.unlink(missing_ok=True)

    if failures:
        print(f"\n{failures} node(s) would be rejected by Palomar's current contract.")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
