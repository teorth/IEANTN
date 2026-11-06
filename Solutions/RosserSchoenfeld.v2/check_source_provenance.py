#!/usr/bin/env python3
"""Check the exact vendored source inventory and hashes; this is not proof verification."""

import hashlib
import json
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent
    provenance = json.loads((root / "source-provenance.json").read_text(encoding="utf-8"))
    recorded: set[str] = set()
    for item in provenance["files"]:
        path = item["path"]
        if path in recorded:
            raise SystemExit(f"Duplicate source entry: {path}")
        recorded.add(path)
        expected_path = "Proof/" + item["module"].replace(".", "/") + ".lean"
        if path != expected_path:
            raise SystemExit(f"Module/path mismatch: {path}")
        expected = item.get("adapted_sha256", item["upstream_sha256"])
        actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Source hash mismatch: {path}")
        for adaptation in item["adaptations"]:
            if not (root / adaptation["patch"]).is_file():
                raise SystemExit(f"Missing adaptation patch for: {path}")
    actual_files = {str(path.relative_to(root)) for path in (root / "Proof").rglob("*.lean")}
    if actual_files != recorded:
        raise SystemExit(
            f"Inventory mismatch: unrecorded={sorted(actual_files - recorded)}, "
            f"missing={sorted(recorded - actual_files)}"
        )
    compatibility = json.loads((root / "compatibility-provenance.json").read_text(encoding="utf-8"))
    helpers = set()
    for item in compatibility["files"]:
        path = item["path"]
        if path in helpers:
            raise SystemExit(f"Duplicate compatibility entry: {path}")
        helpers.add(path)
        if hashlib.sha256((root / path).read_bytes()).hexdigest() != item["sha256"]:
            raise SystemExit(f"Compatibility source hash mismatch: {path}")
    actual_helpers = {
        str(path.relative_to(root)) for path in (root / "RSBoundsCompat").rglob("*.lean")
    }
    if actual_helpers != helpers:
        raise SystemExit("Compatibility helper inventory mismatch")
    print(f"Matched all {len(recorded)} vendored sources and {len(helpers)} compatibility helpers.")


if __name__ == "__main__":
    main()
