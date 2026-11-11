#!/usr/bin/env python3
"""Read-only queries over the versioned IEANTN evidence export.

Pipe ieantn.py export into this command. No query builds Lean, writes metadata,
authenticates a workflow receipt or dispatches a verification.
"""
from __future__ import annotations

import argparse
import copy
import json
import math
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
        parent, queue = {key: None}, deque([key])
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

    def alternative(self, key, justification_id):
        self.require(key)
        old = self.records[key]
        matches = [j for j in old.get("justifications", [])
                   if isinstance(j, dict) and j.get("id") == justification_id]
        if len(matches) != 1:
            raise ValueError("expected exactly one matching justification")
        chosen = matches[0]
        kind = chosen.get("kind")
        if kind not in {"bridged", "lean-comparator", "literature", "asserted",
                        "numerical", "none-yet", "lean-noncompliant"}:
            raise ValueError("unsupported justification kind")
        proposed = copy.deepcopy(self.document)
        entry = next(c for c in proposed["conclusions"] if c["key"] == key)
        entry["designated"], entry["evidence"] = justification_id, kind
        entry["requirements"] = [r for r in entry["requirements"] if r["relation"] == "import"]
        warnings = []
        if kind == "bridged":
            sources = chosen.get("from")
            sources = [sources] if isinstance(sources, str) else sources
            if not isinstance(sources, list) or not sources or any(
                    not isinstance(source, str) for source in sources):
                raise ValueError("bridge must name one or more conclusion sources")
            entry["requirements"] += [{"conclusion": source, "relation": "bridge"}
                                      for source in sorted(set(sources))]
        if kind == "lean-comparator":
            if not entry.get("receipt"):
                entry["evidence"] = "lean-comparator-unassessed"
                warnings.append("The export has no receipt assessment for this spare; "
                                "the hypothetical route remains an unproved leaf.")
            elif entry["receipt"]["state"] == "BROKEN":
                entry["evidence"] = "lean-comparator-drifted"
            elif entry["receipt"]["state"] != "green":
                entry["evidence"] = "lean-comparator-stale"
        after = EvidenceGraph(proposed)
        changes = []
        for current in sorted(self.downstream(key) | after.downstream(key)):
            before_leaves, after_leaves = self.leaves[current], after.leaves[current]
            if before_leaves != after_leaves or current == key:
                changes.append({
                    "conclusion": current, "before": sorted(before_leaves),
                    "after": sorted(after_leaves),
                    "gained": sorted(after_leaves - before_leaves),
                    "discharged": sorted(before_leaves - after_leaves),
                })
        return {"schema_version": 1, "conclusion": key, "justification": justification_id,
                "changes": changes, "warnings": warnings, "writes_metadata": False}


def impact(before, after):
    """Explain structural changes without pretending a graph comparison proves a bridge."""
    changed = {}
    for key in sorted(before.records.keys() | after.records.keys()):
        old, new = before.records.get(key), after.records.get(key)
        reasons = []
        if old is None:
            reasons.append("added")
        elif new is None:
            reasons.append("removed")
        else:
            for field, label in [
                ("fingerprint", "statement"), ("requirements", "requirements"),
                ("designated", "designation"), ("receipt", "receipt-health"),
            ]:
                if old.get(field) != new.get(field):
                    reasons.append(label)
            if before.leaves[key] != after.leaves[key]:
                reasons.append("unproved-leaves")
        if reasons:
            changed[key] = reasons
    findings = []
    for key, reasons in changed.items():
        users = set()
        for graph in (before, after):
            if key in graph.records:
                users.update(graph.downstream(key))
        users.discard(key)
        repairs = []
        if "removed" in reasons and users:
            repairs.append("Migrate surviving consumers before removing the conclusion.")
        if "statement" in reasons:
            old = before.records[key]
            if before.reverse[key] or old.get("receipt"):
                repairs.append("Create a new node version; this statement already has consumers or a receipt.")
            else:
                repairs.append("Review the restated conclusion against its source.")
        if "receipt-health" in reasons:
            repairs.append("Inspect the receipt assessment; only fresh official verification restores a broken receipt.")
        if "requirements" in reasons or "unproved-leaves" in reasons:
            repairs.append("Review every gained leaf; a proposed bridge needs its own checked implication.")
        paths = []
        # Reverse BFS supplies a bounded witness for every downstream result.
        for graph in (before, after):
            if key not in graph.records:
                continue
            queue, parent = deque([key]), {key: None}
            while queue:
                current = queue.popleft()
                for user in sorted(set(graph.reverse[current])):
                    if user not in parent:
                        parent[user] = current
                        queue.append(user)
            for user in sorted(users & parent.keys()):
                route, current = [], user
                while current is not None:
                    route.append(current)
                    current = parent[current]
                paths.append({"conclusion": user, "snapshot": "before" if graph is before else "after",
                              "path_to_changed": route})
        findings.append({"conclusion": key, "reasons": reasons, "downstream": sorted(users),
                         "witness_paths": paths, "repair_advice": repairs})
    return {"schema_version": 1, "changes": findings}


def refresh_plan(graph, costs=None, budget=None):
    """Choose whole-node runs; unknown historical costs never silently fit a finite budget."""
    costs = {} if costs is None else costs
    if not isinstance(costs, dict):
        raise ValueError("costs must map node identifiers to seconds")
    for node, seconds in costs.items():
        if not isinstance(node, str) or type(seconds) not in {int, float} or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError("cost estimates must be finite positive seconds")
    if budget is not None and (type(budget) not in {int, float} or
                               not math.isfinite(budget) or budget <= 0):
        raise ValueError("budget must be finite positive seconds")
    candidates = {}
    for key, entry in graph.records.items():
        receipt = entry.get("receipt")
        state = receipt.get("state") if isinstance(receipt, dict) else None
        if state not in {"yellow", "orange", "churn", "BROKEN"}:
            continue
        node = entry["node"]
        item = candidates.setdefault(node, {"node": node, "conclusions": [],
                                            "states": set(), "downstream": set()})
        item["conclusions"].append(key)
        item["states"].add(state)
        item["downstream"].update(graph.downstream(key))
    used, proposed = 0.0, []
    for item in sorted(candidates.values(), key=lambda c: (
            "BROKEN" not in c["states"], -len(c["downstream"]), c["node"])):
        node, estimate = item["node"], costs.get(item["node"])
        selected = budget is None or estimate is not None and used + estimate <= budget
        reason = "selected"
        if not selected:
            reason = "unknown-cost" if estimate is None else "over-budget"
        if selected and estimate is not None:
            used += estimate
        proposed.append({
            "node": node, "states": sorted(item["states"]),
            "reasons": sorted(item["conclusions"]),
            "covers": sorted(key for key, entry in graph.records.items() if entry["node"] == node),
            "downstream_reach": len(item["downstream"]),
            "estimated_seconds": estimate, "selected": selected, "decision": reason,
        })
    return {"schema_version": 1, "budget_seconds": budget,
            "known_selected_seconds": used, "runs": proposed, "dispatches": False,
            "costs_are_estimates": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=pathlib.Path, help="evidence JSON; default stdin")
    sub = parser.add_subparsers(dest="command", required=True)
    explain = sub.add_parser("explain")
    explain.add_argument("conclusion")
    compare = sub.add_parser("compare")
    compare.add_argument("conclusion")
    compare.add_argument("--justification", required=True)
    changed = sub.add_parser("impact")
    changed.add_argument("--base", type=pathlib.Path, required=True)
    refresh = sub.add_parser("refresh-plan")
    refresh.add_argument("--costs", type=pathlib.Path)
    refresh.add_argument("--budget", type=float)
    args = parser.parse_args()
    try:
        if args.input:
            with args.input.open(encoding="utf-8") as stream:
                graph = EvidenceGraph(load_document(stream))
        else:
            graph = EvidenceGraph(load_document(sys.stdin))
        if args.command == "explain":
            result = graph.explain(args.conclusion)
        elif args.command == "compare":
            result = graph.alternative(args.conclusion, args.justification)
        elif args.command == "impact":
            with args.base.open(encoding="utf-8") as stream:
                result = impact(EvidenceGraph(load_document(stream)), graph)
        else:
            costs = None
            if args.costs:
                with args.costs.open(encoding="utf-8") as stream:
                    costs = load_document(stream)
            result = refresh_plan(graph, costs, args.budget)
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True, allow_nan=False))
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

