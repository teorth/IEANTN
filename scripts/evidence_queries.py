#!/usr/bin/env python3
"""Read-only queries over the versioned IEANTN evidence export.

Pipe ieantn.py export into this command. No query builds Lean, writes metadata,
authenticates a workflow receipt or dispatches a verification.
"""
from __future__ import annotations

import argparse
import copy
import json
import pathlib
import sys
from collections import deque

MAX_CONCLUSIONS = 100_000
VERIFIED = {"lean-comparator", "lean-comparator-stale"}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_document(stream):
    return json.load(stream, object_pairs_hook=unique_object,
                     parse_constant=lambda value: (_ for _ in ()).throw(
                         ValueError(f"non-finite JSON number: {value}")))


class EvidenceGraph:
    """An immutable-by-convention view whose requirement edges are all AND edges."""

    def __init__(self, document):
        if not isinstance(document, dict) or type(document.get("schema_version")) is not int:
            raise ValueError("expected an evidence document with integer schema_version")
        if document["schema_version"] != 1:
            raise ValueError("unsupported evidence schema")
        conclusions = document.get("conclusions")
        if not isinstance(conclusions, list) or len(conclusions) > MAX_CONCLUSIONS:
            raise ValueError("conclusions must be a bounded list")
        self.document = copy.deepcopy(document)
        self.records = {}
        for entry in self.document["conclusions"]:
            if not isinstance(entry, dict) or not isinstance(entry.get("key"), str):
                raise ValueError("each conclusion needs a string key")
            key = entry["key"]
            if key in self.records:
                raise ValueError(f"duplicate conclusion: {key}")
            if not isinstance(entry.get("node"), str) or not isinstance(entry.get("evidence"), str):
                raise ValueError(f"{key}: missing node or evidence")
            if not isinstance(entry.get("requirements"), list):
                raise ValueError(f"{key}: missing requirements")
            self.records[key] = entry
        self.edges = {}
        self.reverse = {key: [] for key in self.records}
        for key, entry in self.records.items():
            edges = []
            for requirement in entry["requirements"]:
                if not isinstance(requirement, dict):
                    raise ValueError(f"{key}: malformed requirement")
                target, relation = requirement.get("conclusion"), requirement.get("relation")
                if not isinstance(target, str) or target not in self.records:
                    raise ValueError(f"{key}: unknown requirement {target}")
                if relation not in {"import", "bridge"}:
                    raise ValueError(f"{key}: unknown requirement relation")
                edges.append((target, relation))
                self.reverse[target].append(key)
            self.edges[key] = sorted(set(edges))
        # Iterative topological order handles long chains without Python recursion limits.
        pending = {key: len({target for target, _ in edges}) for key, edges in self.edges.items()}
        ready = deque(sorted(key for key, count in pending.items() if count == 0))
        self.order = []
        while ready:
            key = ready.popleft()
            self.order.append(key)
            for user in sorted(set(self.reverse[key])):
                pending[user] -= 1
                if pending[user] == 0:
                    ready.append(user)
        if len(self.order) != len(self.records):
            raise ValueError("cycle in combined import and designated-bridge requirements")
        self.leaves = {}
        for key in self.order:
            entry = self.records[key]
            proved = entry["evidence"] in VERIFIED
            receipt = entry.get("receipt")
            if proved and (not isinstance(receipt, dict) or
                           receipt.get("state") not in {"green", "yellow", "orange", "churn"}):
                raise ValueError(f"{key}: verified evidence without a standing receipt assessment")
            leaves = set() if proved or entry["evidence"] == "bridged" else {key}
            for target, _ in self.edges[key]:
                leaves.update(self.leaves[target])
            self.leaves[key] = leaves

    def require(self, key):
        if key not in self.records:
            raise ValueError(f"unknown conclusion: {key}")

    def downstream(self, key):
        self.require(key)
        found, queue = {key}, deque([key])
        while queue:
            current = queue.popleft()
            for user in self.reverse[current]:
                if user not in found:
                    found.add(user)
                    queue.append(user)
        return found

    def explain(self, key):
        self.require(key)
        parent: dict[str, tuple[str, str] | None] = {key: None}
        queue = deque([key])
        while queue:
            current = queue.popleft()
            for target, relation in self.edges[current]:
                if target not in parent:
                    parent[target] = (current, relation)
                    queue.append(target)
        paths = []
        for leaf in sorted(self.leaves[key]):
            path, current = [], leaf
            while True:
                record = self.records[current]
                predecessor = parent[current]
                path.append({
                    "conclusion": current, "evidence": record["evidence"],
                    "receipt": record.get("receipt"), "source": record.get("source"),
                    "via": predecessor[1] if predecessor else None,
                })
                if predecessor is None:
                    break
                current = predecessor[0]
            paths.append({"leaf": leaf, "path": list(reversed(path))})
        return {
            "schema_version": 1, "conclusion": key, "requirements_semantics": "all",
            "unproved_leaves": sorted(self.leaves[key]), "witness_paths": paths,
            "incompletely_traced": sorted(
                current for current in parent
                if self.records[current].get("imports_status") in {"traced", "undetermined"}
            ),
        }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=pathlib.Path, help="evidence JSON; default stdin")
    sub = parser.add_subparsers(dest="command", required=True)
    explain = sub.add_parser("explain")
    explain.add_argument("conclusion")
    args = parser.parse_args()
    try:
        if args.input:
            with args.input.open(encoding="utf-8") as stream:
                graph = EvidenceGraph(load_document(stream))
        else:
            graph = EvidenceGraph(load_document(sys.stdin))
        if args.command == "explain":
            result = graph.explain(args.conclusion)
        else:
            raise ValueError(args.command)
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True, allow_nan=False))
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
