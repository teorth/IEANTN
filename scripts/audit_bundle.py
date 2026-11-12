#!/usr/bin/env python3
"""Write a timestamp-free audit manifest for a generated spin-off directory.

The manifest records sha256 hashes of the project files, the supplied metadata,
the supplied graph snapshot, the hypothesis keys, and a reconstruction note.
Writing it again from the same inputs produces the same bytes. A later check
fails when a recorded file's bytes change.

Hashes identify files. They do not establish that an unproved hypothesis is true.

    python3 scripts/audit_bundle.py write --project DIR --graph graph.json \\
        --metadata meta.json --hypothesis Leaf.v1.main
    python3 scripts/audit_bundle.py check --project DIR
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path


MANIFEST_RELATIVE = "audit/manifest.json"
RECONSTRUCTION_NOTE = (
    "Re-running this command on the same project files, graph snapshot, metadata, "
    "and hypothesis keys reproduces this manifest. It records no timestamps. "
    "sha256 hashes identify file bytes. They do not establish that an unproved "
    "hypothesis is true."
)


class AuditBundleError(Exception):
    """The manifest could not be written or no longer matches the files."""


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def project_files(project: Path) -> list[Path]:
    """Files whose bytes the manifest records, in a stable relative-path order."""
    found: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(project):
        dirnames.sort()
        filenames.sort()
        for name in filenames:
            path = Path(dirpath) / name
            if path.is_symlink():
                continue
            relative = path.relative_to(project).as_posix()
            if relative == MANIFEST_RELATIVE:
                continue
            found.append(path)
    found.sort(key=lambda path: path.relative_to(project).as_posix())
    return found


def _object(value: object, label: str) -> dict:
    if not isinstance(value, dict):
        raise AuditBundleError(f"{label} must be a JSON object")
    return value


def _hypotheses(values: list[str]) -> list[str]:
    if any(not isinstance(item, str) or not item.strip() for item in values):
        raise AuditBundleError("hypothesis keys must be non-empty strings")
    return [item.strip() for item in values]


def build_manifest(
    project: Path,
    graph_bytes: bytes,
    metadata: dict,
    hypotheses: list[str],
) -> dict:
    try:
        graph = json.loads(graph_bytes.decode("utf-8"))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise AuditBundleError(f"graph snapshot is not JSON: {error}") from error
    if isinstance(graph, dict) and any(key in graph for key in ("timestamp", "generated_at", "mtime")):
        raise AuditBundleError("graph snapshot contains a timestamp field; refusing to copy it into the manifest")
    files = [
        {
            "path": path.relative_to(project).as_posix(),
            "sha256": _sha256(path.read_bytes()),
        }
        for path in project_files(project)
    ]
    return {
        "files": files,
        "graph": graph,
        "graph_sha256": _sha256(graph_bytes),
        "hypotheses": _hypotheses(hypotheses),
        "metadata": _object(metadata, "metadata"),
        "reconstruction_note": RECONSTRUCTION_NOTE,
    }


def manifest_bytes(manifest: dict) -> bytes:
    return (json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def write_manifest(
    project: Path,
    graph_path: Path,
    metadata: dict,
    hypotheses: list[str],
) -> bytes:
    if not project.is_dir():
        raise AuditBundleError(f"project directory does not exist: {project}")
    payload = manifest_bytes(build_manifest(project, graph_path.read_bytes(), metadata, hypotheses))
    destination = project / MANIFEST_RELATIVE
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(payload)
    return payload


def check_manifest(project: Path, manifest_path: Path | None = None) -> tuple[bool, str]:
    path = manifest_path or (project / MANIFEST_RELATIVE)
    if not path.is_file():
        return False, f"error: manifest is missing at {path}"
    try:
        recorded = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        return False, f"error: manifest is not JSON: {error}"
    expected = {item["path"]: item["sha256"] for item in recorded.get("files", [])}
    actual_paths = [item.relative_to(project).as_posix() for item in project_files(project)]
    for relative in actual_paths:
        digest = _sha256((project / relative).read_bytes())
        if relative not in expected:
            return False, f"error: {relative} is not in the manifest"
        if expected[relative] != digest:
            return False, f"error: {relative} sha256 does not match the manifest"
    missing = sorted(set(expected) - set(actual_paths))
    if missing:
        return False, f"error: {missing[0]} is missing from the project"
    note = recorded.get("reconstruction_note", "")
    return (
        True,
        f"ok  {len(actual_paths)} files match the manifest. {note}",
    )


def _load_metadata(path: Path) -> dict:
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise AuditBundleError(f"metadata is not JSON: {error}") from error
    return _object(loaded, "metadata")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    write = commands.add_parser("write", help="write audit/manifest.json")
    write.add_argument("--project", required=True, type=Path)
    write.add_argument("--graph", required=True, type=Path)
    write.add_argument("--metadata", required=True, type=Path)
    write.add_argument("--hypothesis", action="append", default=[], help="hypothesis key; repeat for several")
    write.add_argument(
        "--no-hypotheses",
        action="store_true",
        help="record an empty hypothesis list explicitly",
    )
    check = commands.add_parser("check", help="recompute file hashes and compare them to the manifest")
    check.add_argument("--project", required=True, type=Path)
    check.add_argument("--manifest", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "write":
            if not args.hypothesis and not args.no_hypotheses:
                raise AuditBundleError("hypothesis keys were not supplied")
            if args.hypothesis and args.no_hypotheses:
                raise AuditBundleError("pass hypothesis keys or --no-hypotheses, not both")
            payload = write_manifest(
                args.project,
                args.graph,
                _load_metadata(args.metadata),
                list(args.hypothesis),
            )
            sys.stdout.write(f"wrote {args.project / MANIFEST_RELATIVE}\n")
            sys.stdout.write(f"{len(payload)} bytes\n")
            sys.stdout.write(RECONSTRUCTION_NOTE + "\n")
            return 0
        ok, message = check_manifest(args.project, args.manifest)
    except (OSError, AuditBundleError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(message)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
