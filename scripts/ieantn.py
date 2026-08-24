#!/usr/bin/env python3
"""IEANTN network tooling.

One entry point for the checks that keep the node graph honest, plus the challenge generator.

    python scripts/ieantn.py check-closure       import discipline
    python scripts/ieantn.py check-graph         metadata and graph well-formedness
    python scripts/ieantn.py gen-challenges      (re)write every Challenge.lean
    python scripts/ieantn.py gen-challenges --check   fail if any is out of date
    python scripts/ieantn.py report              what each conclusion actually rests on
    python scripts/ieantn.py check               all of the above, in --check mode

None of this runs Comparator; see docs/ARCHITECTURE.md section 4.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("error: PyYAML is required (pip install pyyaml)")

ROOT = pathlib.Path(__file__).resolve().parent.parent
NODES_DIR = ROOT / "IEANTN" / "Nodes"
VOCAB_DIR = ROOT / "IEANTN" / "Vocabulary"

JUSTIFICATION_KINDS = {
    "lean-comparator",
    "numerical",
    "literature",
    "asserted",
    "none-yet",
}

#: Justifications that mean "checked by Lean in this repository". Everything else is a leaf of
#: the trust graph: something the network takes on faith, however reasonably.
VERIFIED_KINDS = {"lean-comparator"}

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)


class Problems:
    """Accumulates failures so one run reports everything, not just the first."""

    def __init__(self) -> None:
        self.items: list[str] = []

    def add(self, where: str, message: str) -> None:
        self.items.append(f"{where}: {message}")

    def report(self, heading: str) -> bool:
        if not self.items:
            print(f"ok  {heading}")
            return True
        print(f"FAIL {heading}")
        for item in self.items:
            print(f"  - {item}")
        return False


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------


def rel(path: pathlib.Path) -> str:
    return path.relative_to(ROOT).as_posix()


def imports_of(path: pathlib.Path) -> list[str]:
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def node_dirs() -> list[pathlib.Path]:
    if not NODES_DIR.is_dir():
        return []
    return sorted(d for d in NODES_DIR.iterdir() if (d / "formalization.yaml").is_file())


def load_nodes() -> dict[str, dict]:
    """node id -> parsed formalization.yaml, with the directory recorded under '_dir'."""
    nodes: dict[str, dict] = {}
    for directory in node_dirs():
        data = yaml.safe_load((directory / "formalization.yaml").read_text(encoding="utf-8"))
        data = data or {}
        data["_dir"] = directory
        nodes[data.get("node", {}).get("id", directory.name)] = data
    return nodes


def conclusions_of(node: dict) -> list[dict]:
    return node.get("conclusions") or []


# ---------------------------------------------------------------------------
# check-closure
# ---------------------------------------------------------------------------


def check_closure() -> bool:
    """Vocabulary and Conclusions may not reach outside Mathlib.

    This is the invariant the whole architecture rests on: a challenge transitively imports
    Vocabulary, so if Vocabulary reached outside Mathlib no node could ever be spun off as a
    standalone Palomar submission. See docs/ARCHITECTURE.md section 2.
    """
    problems = Problems()

    for path in sorted(VOCAB_DIR.rglob("*.lean")):
        for module in imports_of(path):
            if not (module.startswith("Mathlib") or module.startswith("IEANTN.Vocabulary")):
                problems.add(rel(path), f"Vocabulary may import only Mathlib; found `{module}`")

    for directory in node_dirs():
        conclusions = directory / "Conclusions.lean"
        if conclusions.is_file():
            for module in imports_of(conclusions):
                allowed = (
                    module.startswith("Mathlib")
                    or module.startswith("IEANTN.Vocabulary")
                    or (module.startswith("IEANTN.Nodes.") and module.endswith(".Conclusions"))
                )
                if not allowed:
                    problems.add(
                        rel(conclusions),
                        f"a Conclusions file may import only Mathlib, Vocabulary and other "
                        f"Conclusions; found `{module}`",
                    )
        challenge = directory / "Challenge.lean"
        if challenge.is_file():
            for module in imports_of(challenge):
                if not (module.startswith("IEANTN.Nodes.") and module.endswith(".Conclusions")):
                    problems.add(
                        rel(challenge),
                        f"a Challenge file may import only Conclusions files; found `{module}`",
                    )

    return problems.report("import closure")


# ---------------------------------------------------------------------------
# check-graph
# ---------------------------------------------------------------------------


def check_graph() -> bool:
    """Metadata well-formedness, referential integrity, and acyclicity."""
    problems = Problems()
    nodes = load_nodes()

    if not nodes:
        print("ok  node graph (no nodes yet)")
        return True

    for node_id, node in nodes.items():
        where = rel(node["_dir"] / "formalization.yaml")
        meta = node.get("node") or {}

        if meta.get("id") != node["_dir"].name:
            problems.add(where, f"node.id `{meta.get('id')}` != directory `{node['_dir'].name}`")

        seen: set[str] = set()
        for conclusion in conclusions_of(node):
            cid = conclusion.get("id")
            if not cid:
                problems.add(where, "a conclusion has no `id`")
                continue
            if cid in seen:
                problems.add(where, f"duplicate conclusion id `{cid}`")
            seen.add(cid)

            declaration = conclusion.get("declaration", "")
            if declaration != f"{node_id}.{cid}":
                problems.add(
                    where,
                    f"conclusion `{cid}`: declaration should be `{node_id}.{cid}`, "
                    f"found `{declaration}`",
                )

            expected_challenge = f"{node_id}.challenge_{cid}"
            if conclusion.get("challenge") != expected_challenge:
                problems.add(
                    where,
                    f"conclusion `{cid}`: challenge should be `{expected_challenge}`",
                )

            kind = (conclusion.get("justification") or {}).get("kind")
            if kind not in JUSTIFICATION_KINDS:
                problems.add(
                    where,
                    f"conclusion `{cid}`: justification.kind `{kind}` is not one of "
                    + ", ".join(sorted(JUSTIFICATION_KINDS)),
                )
            if kind == "lean-comparator" and conclusion.get("receipt") is None:
                problems.add(
                    where,
                    f"conclusion `{cid}`: justification is `lean-comparator` but no receipt is "
                    "recorded",
                )

            for dependency in conclusion.get("imports") or []:
                target_node = dependency.get("node")
                target_conclusion = dependency.get("conclusion")
                if target_node not in nodes:
                    problems.add(
                        where, f"conclusion `{cid}` imports unknown node `{target_node}`"
                    )
                    continue
                known = {c.get("id") for c in conclusions_of(nodes[target_node])}
                if target_conclusion not in known:
                    problems.add(
                        where,
                        f"conclusion `{cid}` imports `{target_node}.{target_conclusion}`, "
                        "which that node does not export",
                    )

    # Acyclicity, at conclusion granularity.
    edges: dict[str, list[str]] = {}
    for node_id, node in nodes.items():
        for conclusion in conclusions_of(node):
            key = f"{node_id}.{conclusion.get('id')}"
            edges[key] = [
                f"{d.get('node')}.{d.get('conclusion')}"
                for d in (conclusion.get("imports") or [])
            ]

    WHITE, GREY, BLACK = 0, 1, 2
    colour = {key: WHITE for key in edges}

    def visit(key: str, trail: list[str]) -> None:
        colour[key] = GREY
        for target in edges.get(key, []):
            if target not in colour:
                continue
            if colour[target] == GREY:
                cycle = " -> ".join(trail + [key, target])
                problems.add("graph", f"import cycle: {cycle}")
            elif colour[target] == WHITE:
                visit(target, trail + [key])
        colour[key] = BLACK

    for key in sorted(edges):
        if colour[key] == WHITE:
            visit(key, [])

    return problems.report("node graph")


# ---------------------------------------------------------------------------
# gen-challenges
# ---------------------------------------------------------------------------


def hypothesis_name(dependency: dict) -> str:
    return f"{dependency.get('node')}_{dependency.get('conclusion')}".lower()


def render_challenge(node_id: str, node: dict) -> str:
    authors = ", ".join((node.get("project") or {}).get("authors") or ["IEANTN contributors"])

    needed = {f"IEANTN.Nodes.{node_id}.Conclusions"}
    for conclusion in conclusions_of(node):
        for dependency in conclusion.get("imports") or []:
            needed.add(f"IEANTN.Nodes.{dependency.get('node')}.Conclusions")

    lines = [
        "/-",
        "Copyright (c) 2026 IEANTN contributors. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        f"Authors: {authors}",
        "-/",
    ]
    lines += [f"import {module}" for module in sorted(needed)]
    lines += [
        "",
        "/-!",
        f"# Challenge: `{node_id}`",
        "",
        "**Generated file - do not edit.**  Regenerated by",
        "`python scripts/ieantn.py gen-challenges` from `Conclusions.lean` and",
        "`formalization.yaml`; CI diffs the two.",
        "",
        "Each `sorry` below is deliberate and permanent: a challenge *states*, it does not prove.",
        "How each conclusion is justified is recorded in `formalization.yaml`, not here.",
        "-/",
        "",
    ]

    for conclusion in conclusions_of(node):
        cid = conclusion.get("id")
        binders = "".join(
            f"\n    ({hypothesis_name(d)} : {d.get('node')}.{d.get('conclusion')})"
            for d in (conclusion.get("imports") or [])
        )
        if binders:
            lines.append(f"theorem {node_id}.challenge_{cid}{binders} :")
            lines.append(f"    {node_id}.{cid} := by")
        else:
            lines.append(f"theorem {node_id}.challenge_{cid} : {node_id}.{cid} := by")
        lines.append("  sorry")
        lines.append("")

    return "\n".join(lines).rstrip("\n") + "\n"


def gen_challenges(check_only: bool) -> bool:
    problems = Problems()
    nodes = load_nodes()
    for node_id, node in nodes.items():
        path = node["_dir"] / "Challenge.lean"
        rendered = render_challenge(node_id, node)
        if check_only:
            current = path.read_text(encoding="utf-8") if path.is_file() else ""
            if current != rendered:
                problems.add(
                    rel(path),
                    "out of date; run `python scripts/ieantn.py gen-challenges`",
                )
        else:
            path.write_text(rendered, encoding="utf-8", newline="\n")
            print(f"wrote {rel(path)}")
    if check_only:
        return problems.report("generated challenges")
    return True


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


def report() -> bool:
    """For every conclusion, what it actually rests on.

    This is the headline output of the repository: the transitive set of claims a result depends
    on that are *not* proved in Lean here.
    """
    nodes = load_nodes()
    index: dict[str, tuple[str, dict]] = {}
    for node_id, node in nodes.items():
        for conclusion in conclusions_of(node):
            index[f"{node_id}.{conclusion.get('id')}"] = (node_id, conclusion)

    fan_in: dict[str, int] = {key: 0 for key in index}

    def leaves(key: str, seen: set[str]) -> set[str]:
        if key in seen or key not in index:
            return set()
        seen.add(key)
        _, conclusion = index[key]
        kind = (conclusion.get("justification") or {}).get("kind")
        dependencies = [
            f"{d.get('node')}.{d.get('conclusion')}" for d in (conclusion.get("imports") or [])
        ]
        result: set[str] = set()
        if kind not in VERIFIED_KINDS:
            result.add(f"{key}  [{kind}]")
        for dependency in dependencies:
            fan_in[dependency] = fan_in.get(dependency, 0) + 1
            result |= leaves(dependency, seen)
        return result

    print("Unproved-in-Lean dependencies, per conclusion")
    print("=" * 60)
    for key in sorted(index):
        rests_on = sorted(leaves(key, set()))
        print(f"\n{key}")
        if not rests_on:
            print("  fully verified in Lean")
        for item in rests_on:
            print(f"  - {item}")

    ranked = sorted(((count, key) for key, count in fan_in.items() if count), reverse=True)
    if ranked:
        print("\n\nLeverage (fan-in): refresh these first")
        print("=" * 60)
        for count, key in ranked:
            print(f"  {count:3d}  {key}")
    return True


# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("check-closure")
    sub.add_parser("check-graph")
    generate = sub.add_parser("gen-challenges")
    generate.add_argument("--check", action="store_true", help="fail instead of rewriting")
    sub.add_parser("report")
    sub.add_parser("check", help="every check, in --check mode")

    args = parser.parse_args()
    if args.command == "check-closure":
        return 0 if check_closure() else 1
    if args.command == "check-graph":
        return 0 if check_graph() else 1
    if args.command == "gen-challenges":
        return 0 if gen_challenges(args.check) else 1
    if args.command == "report":
        return 0 if report() else 1
    if args.command == "check":
        results = [check_closure(), check_graph(), gen_challenges(True)]
        return 0 if all(results) else 1
    return 2


if __name__ == "__main__":
    sys.exit(main())
