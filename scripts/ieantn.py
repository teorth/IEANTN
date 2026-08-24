#!/usr/bin/env python3
"""IEANTN network tooling.

One entry point for the checks that keep the node graph honest, the challenge generator, and the
routine node-management tasks.

    python scripts/ieantn.py check-closure           import discipline
    python scripts/ieantn.py check-graph             metadata and graph well-formedness
    python scripts/ieantn.py gen-challenges          (re)write every Challenge.lean
    python scripts/ieantn.py gen-challenges --check  fail if any is out of date
    python scripts/ieantn.py report                  what each conclusion actually rests on
    python scripts/ieantn.py fingerprint             recompute the statement fingerprints
    python scripts/ieantn.py fingerprint --check     fail if any has moved
    python scripts/ieantn.py status                  the traffic light for every conclusion
    python scripts/ieantn.py housekeeping            the derived task queue
    python scripts/ieantn.py check                   every check, in --check mode

    python scripts/ieantn.py new-node FKS2           scaffold a brand-new node at v1
    python scripts/ieantn.py new-version Lcm         scaffold Lcm.v2 from the latest version
    python scripts/ieantn.py deprecate Lcm.v1 --for Lcm.v2

Nodes are versioned: a node lives at `IEANTN/Nodes/<Family>/<version>/` and its id is
`<Family>.<version>`, e.g. `Lcm.v1`. Editing a conclusion's statement in place is only safe while
nothing depends on it; otherwise make a new version. See docs/ARCHITECTURE.md.

None of this runs Comparator.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import re
import shutil
import sys

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("error: PyYAML is required (pip install pyyaml)")

ROOT = pathlib.Path(__file__).resolve().parent.parent
NODES_DIR = ROOT / "IEANTN" / "Nodes"
VOCAB_DIR = ROOT / "IEANTN" / "Vocabulary"
FINGERPRINTS = ROOT / "fingerprints.json"
RECEIPTS = ROOT / "receipts"

#: Toolchain minor releases behind current, past which a refresh is assumed to fall outside the
#: Mathlib cache window and cost many times the per-node budget. A heuristic, not a measurement.
CACHE_WINDOW_RELEASES = 2

#: A justification that stands on its own evidence.
PRIMITIVE_KINDS = {"lean-comparator", "numerical", "literature", "asserted", "none-yet"}
#: A justification borrowed from another version via a proved bridge.
DERIVED_KINDS = {"bridged"}
JUSTIFICATION_KINDS = PRIMITIVE_KINDS | DERIVED_KINDS

#: Kinds meaning "checked by Lean in this repository". Everything else is a leaf of the trust
#: graph: something the network takes on faith, however reasonably.
VERIFIED_KINDS = {"lean-comparator"}

NODE_STATUSES = {"template", "stub", "awaiting-solution", "active", "deprecated"}

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)
VERSION_RE = re.compile(r"^v(\d+)$")


class Problems:
    """Accumulates failures so one run reports everything, not just the first."""

    def __init__(self) -> None:
        self.errors: list[str] = []
        self.warnings: list[str] = []

    def add(self, where: str, message: str) -> None:
        self.errors.append(f"{where}: {message}")

    def warn(self, where: str, message: str) -> None:
        self.warnings.append(f"{where}: {message}")

    def report(self, heading: str) -> bool:
        for item in self.warnings:
            print(f"warn {heading}: {item}")
        if not self.errors:
            print(f"ok  {heading}")
            return True
        print(f"FAIL {heading}")
        for item in self.errors:
            print(f"  - {item}")
        return False


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------


def rel(path: pathlib.Path) -> str:
    return path.relative_to(ROOT).as_posix()


def imports_of(path: pathlib.Path) -> list[str]:
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def node_id_of(directory: pathlib.Path) -> str:
    """`IEANTN/Nodes/Lcm/v1` -> `Lcm.v1`."""
    return directory.relative_to(NODES_DIR).as_posix().replace("/", ".")


def node_dirs() -> list[pathlib.Path]:
    if not NODES_DIR.is_dir():
        return []
    return sorted(p.parent for p in NODES_DIR.rglob("formalization.yaml"))


def load_nodes() -> dict[str, dict]:
    """node id -> parsed formalization.yaml, with the directory recorded under '_dir'."""
    nodes: dict[str, dict] = {}
    for directory in node_dirs():
        data = yaml.safe_load((directory / "formalization.yaml").read_text(encoding="utf-8")) or {}
        data["_dir"] = directory
        nodes[node_id_of(directory)] = data
    return nodes


def conclusions_of(node: dict) -> list[dict]:
    return node.get("conclusions") or []


def justifications_of(conclusion: dict) -> list[dict]:
    """Every justification available for a conclusion, designated or not."""
    return conclusion.get("justifications") or []


def designated_of(conclusion: dict) -> dict | None:
    """The one justification of record.

    A conclusion may have several independent grounds -- a paper, a Lean solution, a bridge from
    another version -- and recording them all is worth doing: they are evidence diversity, and a
    spare when the designated one goes stale. But exactly one is *designated*, and only designated
    justifications carry trust.

    That is what keeps the transport check simple and the dependency report meaningful. Designation
    is a function, so the designated-transport graph has out-degree one and plain acyclicity is
    exactly the right condition; and the report can answer "what does this rest on" with one chain
    instead of a disjunction over every chain that happens to exist.
    """
    wanted = conclusion.get("designated")
    for justification in justifications_of(conclusion):
        if justification.get("id") == wanted:
            return justification
    return None


def designated_kind(conclusion: dict) -> str | None:
    justification = designated_of(conclusion)
    return justification.get("kind") if justification else None


def edit_yaml(path: pathlib.Path):
    """Load a node yaml for *modification*, preserving comments.

    Reading uses PyYAML, which is enough for the checks and is all CI needs. Writing must not:
    `yaml.safe_dump` silently discards every comment, and in these files the comments carry the
    mathematical provenance -- which source proves what, what was verified and what was assumed,
    what a later reader must double-check. Losing them is a real loss, so the mutating commands
    require ruamel and round-trip instead.
    """
    try:
        from ruamel.yaml import YAML
    except ImportError:  # pragma: no cover
        sys.exit(
            "error: the node-editing commands need ruamel.yaml, which preserves comments\n"
            "       (pip install ruamel.yaml).  The read-only checks do not."
        )
    writer = YAML()
    writer.preserve_quotes = True
    writer.width = 100
    return writer, writer.load(path.read_text(encoding="utf-8"))


def versions_of(family: str) -> list[tuple[int, pathlib.Path]]:
    """Every version directory of a family, ordered by version number."""
    family_dir = NODES_DIR / family
    if not family_dir.is_dir():
        return []
    found = []
    for child in family_dir.iterdir():
        match = VERSION_RE.match(child.name)
        if match and (child / "formalization.yaml").is_file():
            found.append((int(match.group(1)), child))
    return sorted(found)


# ---------------------------------------------------------------------------
# check-closure
# ---------------------------------------------------------------------------


def check_closure() -> bool:
    """Vocabulary and Conclusions may not reach outside Mathlib.

    This is the invariant the architecture rests on: a challenge transitively imports Vocabulary,
    so if Vocabulary reached outside Mathlib no node could be spun off as a standalone Palomar
    submission. See docs/ARCHITECTURE.md section 2.
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
                ok = (
                    module.startswith("Mathlib")
                    or module.startswith("IEANTN.Vocabulary")
                    or (module.startswith("IEANTN.Nodes.") and module.endswith(".Conclusions"))
                )
                if not ok:
                    problems.add(
                        rel(conclusions),
                        "a Conclusions file may import only Mathlib, Vocabulary and other "
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


def _check_acyclic(edges: dict[str, list[str]], problems: Problems, label: str) -> None:
    WHITE, GREY, BLACK = 0, 1, 2
    colour = {key: WHITE for key in edges}

    def visit(key: str, trail: list[str]) -> None:
        colour[key] = GREY
        for target in edges.get(key, []):
            if target not in colour:
                continue
            if colour[target] == GREY:
                problems.add("graph", f"{label} cycle: {' -> '.join(trail + [key, target])}")
            elif colour[target] == WHITE:
                visit(target, trail + [key])
        colour[key] = BLACK

    for key in sorted(edges):
        if colour[key] == WHITE:
            visit(key, [])


def check_graph() -> bool:
    """Metadata well-formedness, referential integrity, and the two acyclicity conditions.

    Three relations, three different rules:

    * **imports** must be acyclic -- trust flows along them;
    * **bridges** need not be, and are deliberately bidirectional;
    * **justification transport** (`bridged`) must be acyclic, or two versions can each borrow
      their justification from the other and neither is justified by anything.
    """
    problems = Problems()
    nodes = load_nodes()

    if not nodes:
        print("ok  node graph (no nodes yet)")
        return True

    for node_id, node in nodes.items():
        where = rel(node["_dir"] / "formalization.yaml")
        meta = node.get("node") or {}

        if meta.get("id") != node_id:
            problems.add(where, f"node.id `{meta.get('id')}` != path-derived id `{node_id}`")
        status = meta.get("status")
        if status is not None and status not in NODE_STATUSES:
            problems.add(where, f"node.status `{status}` is not one of {sorted(NODE_STATUSES)}")
        if status == "template":
            problems.add(
                where,
                "this node is still the scaffolded template. Fill in the conclusions, the "
                "sources and the project fields, then change `node.status`. (The template is "
                "designed to build locally but fail here, so an unfinished node cannot be "
                "merged by accident.)",
            )
        if status == "deprecated":
            replacement = meta.get("superseded_by")
            if not replacement:
                problems.add(where, "a deprecated node must name `node.superseded_by`")
            elif replacement not in nodes:
                problems.add(where, f"node.superseded_by `{replacement}` does not exist")

        seen: set[str] = set()
        for conclusion in conclusions_of(node):
            cid = conclusion.get("id")
            if not cid:
                problems.add(where, "a conclusion has no `id`")
                continue
            if cid in seen:
                problems.add(where, f"duplicate conclusion id `{cid}`")
            seen.add(cid)

            if conclusion.get("declaration") != f"{node_id}.{cid}":
                problems.add(
                    where,
                    f"conclusion `{cid}`: declaration should be `{node_id}.{cid}`, "
                    f"found `{conclusion.get('declaration')}`",
                )
            if conclusion.get("challenge") != f"{node_id}.challenge_{cid}":
                problems.add(
                    where, f"conclusion `{cid}`: challenge should be `{node_id}.challenge_{cid}`"
                )

            available = justifications_of(conclusion)
            if not available:
                problems.add(where, f"conclusion `{cid}`: needs at least one justification")
            seen_ids: set[str] = set()
            for justification in available:
                jid = justification.get("id")
                if not jid:
                    problems.add(where, f"conclusion `{cid}`: a justification has no `id`")
                    continue
                if jid in seen_ids:
                    problems.add(where, f"conclusion `{cid}`: duplicate justification id `{jid}`")
                seen_ids.add(jid)

                kind = justification.get("kind")
                if kind not in JUSTIFICATION_KINDS:
                    problems.add(
                        where,
                        f"conclusion `{cid}`, justification `{jid}`: kind `{kind}` is not one of "
                        + ", ".join(sorted(JUSTIFICATION_KINDS)),
                    )
                if kind == "lean-comparator":
                    key = f"{node_id}.{cid}"
                    receipt = load_receipt(key)
                    if receipt is None:
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: `lean-comparator` but "
                            f"{rel(receipt_path(key))} does not exist. Receipts are written by "
                            "the verification workflow, not by hand.",
                        )
                    elif receipt.get("conclusion") != key:
                        problems.add(
                            where,
                            f"conclusion `{cid}`: {rel(receipt_path(key))} records "
                            f"`{receipt.get('conclusion')}`",
                        )
                if kind == "bridged":
                    if not justification.get("from"):
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: `bridged` must name "
                            "`from`",
                        )
                    if not justification.get("bridge"):
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: `bridged` must name the "
                            "`bridge` file",
                        )
                    elif not (ROOT / justification["bridge"]).is_file():
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: bridge file "
                            f"`{justification['bridge']}` is missing",
                        )

            if available and designated_of(conclusion) is None:
                problems.add(
                    where,
                    f"conclusion `{cid}`: `designated` is `{conclusion.get('designated')}`, which "
                    f"is not one of its justification ids ({sorted(seen_ids)})",
                )
            elif designated_kind(conclusion) == "none-yet" and len(available) > 1:
                problems.warn(
                    where,
                    f"conclusion `{cid}` designates a `none-yet` justification while others are "
                    "available; designate one of those instead",
                )

            for dependency in conclusion.get("imports") or []:
                target_node = dependency.get("node")
                target_conclusion = dependency.get("conclusion")
                if target_node not in nodes:
                    problems.add(where, f"conclusion `{cid}` imports unknown node `{target_node}`")
                    continue
                known = {c.get("id") for c in conclusions_of(nodes[target_node])}
                if target_conclusion not in known:
                    problems.add(
                        where,
                        f"conclusion `{cid}` imports `{target_node}.{target_conclusion}`, "
                        "which that node does not export",
                    )
                elif (nodes[target_node].get("node") or {}).get("status") == "deprecated":
                    problems.warn(
                        where,
                        f"conclusion `{cid}` imports deprecated `{target_node}`; prefer "
                        f"`{(nodes[target_node].get('node') or {}).get('superseded_by')}`",
                    )

    import_edges: dict[str, list[str]] = {}
    transport_edges: dict[str, list[str]] = {}
    for node_id, node in nodes.items():
        for conclusion in conclusions_of(node):
            key = f"{node_id}.{conclusion.get('id')}"
            import_edges[key] = [
                f"{d.get('node')}.{d.get('conclusion')}"
                for d in (conclusion.get("imports") or [])
            ]
            # Only the *designated* justification carries trust, so only it can create a
            # transport edge. Designation is a function, so this graph has out-degree at most
            # one and plain acyclicity is exactly the condition needed.
            justification = designated_of(conclusion) or {}
            transport_edges[key] = (
                [justification["from"]] if justification.get("kind") == "bridged"
                and justification.get("from") else []
            )

    _check_acyclic(import_edges, problems, "import")
    _check_acyclic(transport_edges, problems, "justification-transport")

    return problems.report("node graph")


# ---------------------------------------------------------------------------
# gen-challenges
# ---------------------------------------------------------------------------


def module_of(node_id: str) -> str:
    return f"IEANTN.Nodes.{node_id}.Conclusions"


def hypothesis_name(dependency: dict) -> str:
    return f"{dependency.get('node')}_{dependency.get('conclusion')}".replace(".", "_").lower()


def render_challenge(node_id: str, node: dict) -> str:
    authors = ", ".join((node.get("project") or {}).get("authors") or ["IEANTN contributors"])
    needed = {module_of(node_id)}
    for conclusion in conclusions_of(node):
        for dependency in conclusion.get("imports") or []:
            needed.add(module_of(str(dependency.get("node"))))

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
        lines += ["  sorry", ""]

    return "\n".join(lines).rstrip("\n") + "\n"


def gen_challenges(check_only: bool) -> bool:
    problems = Problems()
    for node_id, node in load_nodes().items():
        path = node["_dir"] / "Challenge.lean"
        rendered = render_challenge(node_id, node)
        if check_only:
            if (path.read_text(encoding="utf-8") if path.is_file() else "") != rendered:
                problems.add(rel(path), "out of date; run `python scripts/ieantn.py gen-challenges`")
        else:
            path.write_text(rendered, encoding="utf-8", newline="\n")
            print(f"wrote {rel(path)}")
    return problems.report("generated challenges") if check_only else True


# ---------------------------------------------------------------------------
# fingerprint
# ---------------------------------------------------------------------------


def compute_fingerprints() -> dict[str, str]:
    """Ask Lean for each conclusion's canonical statement text, and digest it.

    The digest is kept here rather than in Lean so the algorithm is easy to change and Lean needs
    no cryptographic primitive. See `Tools/Hash.lean` for what is actually fingerprinted, and in
    particular for the one kind of change it deliberately cannot see.
    """
    declarations = sorted(
        f"{node_id}.{conclusion.get('id')}"
        for node_id, node in load_nodes().items()
        for conclusion in conclusions_of(node)
    )
    if not declarations:
        return {}
    finished = subprocess.run(
        ["lake", "exe", "ieantn_hash", *declarations],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if finished.returncode != 0:
        sys.exit(
            "error: could not compute fingerprints. Is the project built?\n"
            "       try `lake build ieantn_hash`\n" + (finished.stderr or "").strip()
        )
    payload = next(
        (line for line in reversed(finished.stdout.splitlines()) if line.startswith("{")), None
    )
    if payload is None:
        sys.exit("error: ieantn_hash produced no output")
    return {
        name: hashlib.sha256(text.encode("utf-8")).hexdigest()
        for name, text in json.loads(payload).items()
    }


def fingerprint(check_only: bool) -> bool:
    """Maintain `fingerprints.json`.

    Committing the fingerprints has a purpose beyond bookkeeping: it makes **every change of
    mathematical meaning show up as a diff line**, including ones whose Lean edit looks cosmetic.
    A reviewer can see that a statement moved without having to elaborate anything.
    """
    current = compute_fingerprints()
    recorded = json.loads(FINGERPRINTS.read_text(encoding="utf-8")) if FINGERPRINTS.is_file() else {}

    if not check_only:
        FINGERPRINTS.write_text(
            json.dumps(current, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
        )
        for name, digest in sorted(current.items()):
            marker = " " if recorded.get(name) == digest else "*"
            print(f"{marker} {digest[:16]}  {name}")
        print(f"\nwrote {rel(FINGERPRINTS)}")
        return True

    problems = Problems()
    for name, digest in sorted(current.items()):
        if name not in recorded:
            problems.add(name, "no recorded fingerprint; run `ieantn.py fingerprint`")
        elif recorded[name] != digest:
            problems.add(
                name,
                f"statement changed: recorded {recorded[name][:16]}, now {digest[:16]}. "
                "If this was intended, run `ieantn.py fingerprint`; if the conclusion has "
                "dependants, make a new version instead.",
            )
    for name in sorted(set(recorded) - set(current)):
        problems.warn(name, "recorded fingerprint has no matching conclusion any more")
    return problems.report("statement fingerprints")


# ---------------------------------------------------------------------------
# receipts and status
# ---------------------------------------------------------------------------


def current_environment() -> dict:
    """The environment a verification run today would happen in."""
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(
        (
            package.get("rev")
            for package in manifest.get("packages", [])
            if package.get("name") == "mathlib"
        ),
        None,
    )
    return {
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "mathlib_rev": mathlib,
    }


def receipt_path(conclusion_key: str) -> pathlib.Path:
    return RECEIPTS / f"{conclusion_key}.json"


def load_receipt(conclusion_key: str) -> dict | None:
    path = receipt_path(conclusion_key)
    if not path.is_file():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def release_distance(recorded: str, current: str) -> int | None:
    """How many Lean minor releases apart two toolchain strings are, if it can be told."""
    pattern = re.compile(r"v(\d+)\.(\d+)\.")
    left, right = pattern.search(recorded or ""), pattern.search(current or "")
    if not left or not right:
        return None
    return abs(
        (int(right.group(1)), int(right.group(2)))[1] - (int(left.group(1)), int(left.group(2)))[1]
    )


def assess(conclusion_key: str, receipt: dict, fingerprints: dict[str, str]) -> tuple[str, str]:
    """Grade one receipt against the world as it is now.

    Two axes, deliberately not collapsed (ARCHITECTURE section 4):

    * a **statement** that has moved is a *broken edge* -- the verified implication no longer
      connects to what is now claimed. Binary and fatal, however small the edit;
    * an **environment** that has moved is ordinary staleness. Graduated, and expected.
    """
    recorded = receipt.get("statement") or {}
    for name, digest in sorted(recorded.items()):
        now = fingerprints.get(name)
        if now is None:
            return "BROKEN", f"`{name}` no longer exists"
        if now != digest:
            which = "its own statement" if name == conclusion_key else f"`{name}`"
            return "BROKEN", f"{which} changed since verification"

    environment = receipt.get("environment") or {}
    current = current_environment()
    if environment.get("mathlib_rev") == current["mathlib_rev"]:
        return "green", "verified against the current environment"

    recorded_toolchain = environment.get("lean_toolchain", "?")
    distance = release_distance(recorded_toolchain, current["lean_toolchain"])
    detail = f"verified under {recorded_toolchain}, now {current['lean_toolchain']}"
    if distance is not None and distance > CACHE_WINDOW_RELEASES:
        return "orange", f"{detail} ({distance} releases; likely outside the cache window)"
    return "yellow", detail


def status() -> bool:
    """The traffic light for every conclusion."""
    nodes = load_nodes()
    fingerprints = compute_fingerprints()
    lights = {"green": 0, "yellow": 0, "orange": 0, "BROKEN": 0, "-": 0}

    print("Conclusion status")
    print("=" * 78)
    for node_id, node in sorted(nodes.items()):
        for conclusion in conclusions_of(node):
            key = f"{node_id}.{conclusion.get('id')}"
            kind = designated_kind(conclusion)
            if kind != "lean-comparator":
                lights["-"] += 1
                print(f"  -       {key}")
                print(f"          not Lean-verified here; designated `{kind}`")
                continue
            receipt = load_receipt(key)
            if receipt is None:
                lights["BROKEN"] += 1
                print(f"  BROKEN  {key}")
                print("          designated `lean-comparator` but no receipt file")
                continue
            light, detail = assess(key, receipt, fingerprints)
            lights[light] += 1
            print(f"  {light:<7} {key}")
            print(f"          {detail}")

    print("\n" + "=" * 78)
    print(
        "  ".join(f"{name}: {count}" for name, count in lights.items() if count)
        or "  nothing recorded"
    )
    if lights["BROKEN"]:
        print("\nA BROKEN receipt is not staleness: the verified implication no longer connects")
        print("to what the node now claims. Re-verify, or make a new version.")
    return True


def record_receipt(conclusion_key: str, solution: str, run_url: str, stamp: str) -> bool:
    """Write a receipt. **Run by the verification workflow, never by an author.**

    An author-written receipt is worth nothing -- it is a claim of verification typed by the
    person making the claim. The protection is not this function refusing to run; it is that
    `receipts/` is writable only by the verification workflow's identity, enforced by a ruleset
    path restriction, and that a receipt arriving in a PR from anyone else is a review failure.
    """
    nodes = load_nodes()
    index = index_conclusions(nodes)
    if conclusion_key not in index:
        print(f"error: unknown conclusion `{conclusion_key}`")
        return False
    _, conclusion = index[conclusion_key]

    wanted = [conclusion_key] + [
        f"{d.get('node')}.{d.get('conclusion')}" for d in (conclusion.get("imports") or [])
    ]
    fingerprints = compute_fingerprints()
    missing = [name for name in wanted if name not in fingerprints]
    if missing:
        print(f"error: no fingerprint for {missing}")
        return False

    RECEIPTS.mkdir(exist_ok=True)
    receipt = {
        "schema": 1,
        "conclusion": conclusion_key,
        "challenge": conclusion.get("challenge"),
        "statement": {name: fingerprints[name] for name in wanted},
        "environment": current_environment(),
        "solution": {"project": solution},
        "run": {"workflow_run": run_url, "recorded_at": stamp},
    }
    path = receipt_path(conclusion_key)
    path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"wrote {rel(path)}")
    return True


# ---------------------------------------------------------------------------
# report / housekeeping
# ---------------------------------------------------------------------------


def index_conclusions(nodes: dict[str, dict]) -> dict[str, tuple[str, dict]]:
    index: dict[str, tuple[str, dict]] = {}
    for node_id, node in nodes.items():
        for conclusion in conclusions_of(node):
            index[f"{node_id}.{conclusion.get('id')}"] = (node_id, conclusion)
    return index


def importers_of(nodes: dict[str, dict]) -> dict[str, list[str]]:
    """conclusion key -> the conclusion keys that import it."""
    result: dict[str, list[str]] = {}
    for node_id, node in nodes.items():
        for conclusion in conclusions_of(node):
            key = f"{node_id}.{conclusion.get('id')}"
            for dependency in conclusion.get("imports") or []:
                target = f"{dependency.get('node')}.{dependency.get('conclusion')}"
                result.setdefault(target, []).append(key)
    return result


def report() -> bool:
    """For every conclusion, the transitive set of claims it rests on that Lean has not checked."""
    nodes = load_nodes()
    index = index_conclusions(nodes)
    importers = importers_of(nodes)

    def leaves(key: str, seen: set[str]) -> set[str]:
        if key in seen or key not in index:
            return set()
        seen.add(key)
        _, conclusion = index[key]
        justification = designated_of(conclusion) or {}
        kind = justification.get("kind")
        spares = len(justifications_of(conclusion)) - 1
        result: set[str] = set()
        if kind == "bridged":
            result |= leaves(justification.get("from", ""), seen)
        elif kind not in VERIFIED_KINDS:
            note = f"  [{kind}]" + (f", {spares} other justification(s) available" if spares else "")
            result.add(f"{key}{note}")
        for dependency in conclusion.get("imports") or []:
            result |= leaves(f"{dependency.get('node')}.{dependency.get('conclusion')}", seen)
        return result

    print("Unproved-in-Lean dependencies, per conclusion")
    print("=" * 62)
    for key in sorted(index):
        rests_on = sorted(leaves(key, set()))
        print(f"\n{key}")
        for item in rests_on or ["  fully verified in Lean"]:
            print(f"  - {item}" if rests_on else item)

    ranked = sorted(((len(v), k) for k, v in importers.items()), reverse=True)
    if ranked:
        print("\n\nLeverage (fan-in): refresh these first")
        print("=" * 62)
        for count, key in ranked:
            print(f"  {count:3d}  {key}")
    return True


def housekeeping() -> bool:
    """The task queue, derived from graph state rather than maintained by hand."""
    nodes = load_nodes()
    importers = importers_of(nodes)
    tasks: list[str] = []

    for node_id, node in sorted(nodes.items()):
        meta = node.get("node") or {}
        if meta.get("status") == "deprecated":
            users = sorted(
                {u for c in conclusions_of(node)
                 for u in importers.get(f"{node_id}.{c.get('id')}", [])}
            )
            replacement = meta.get("superseded_by")
            if users:
                for user in users:
                    tasks.append(f"migrate  {user}  off deprecated {node_id} -> {replacement}")
            else:
                tasks.append(f"delete   {node_id}  (deprecated, nothing imports it)")
        for conclusion in conclusions_of(node):
            kind = designated_kind(conclusion)
            if kind == "none-yet":
                tasks.append(f"justify  {node_id}.{conclusion.get('id')}  (none-yet)")
            elif kind in {"literature", "asserted"}:
                tasks.append(f"formalize {node_id}.{conclusion.get('id')}  ({kind})")

    print("Housekeeping queue")
    print("=" * 62)
    for task in tasks or ["  nothing outstanding"]:
        print(f"  {task}" if tasks else task)
    return True


# ---------------------------------------------------------------------------
# new-version / deprecate
# ---------------------------------------------------------------------------


CONCLUSIONS_TEMPLATE = """\
/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO
-/
import IEANTN.Vocabulary

/-!
# Node `{family}`

TODO: one paragraph saying what this node is about, and citing its source.

Then replace `replace_me` below with the node's real conclusions, and fill in
`formalization.yaml`.  Until `node.status` is changed away from `template`,
`python scripts/ieantn.py check-graph` will refuse this node -- deliberately, so that an
unfinished scaffold cannot be merged by accident.
-/

namespace {family}.v1

/-- TODO: replace this placeholder with a real conclusion.

Every conclusion is a `def _ : Prop`, never a `structure`, and its docstring is where the
informal statement lives -- there is no blueprint.  State the source's own numbering, its
hypotheses, and anything a transcriber could get wrong. -/
def replace_me : Prop := True

end {family}.v1
"""

YAML_TEMPLATE = """\
# Node metadata for `{family}.v1`.  See docs/NODES.md.
version: "v0.4"

node:
  id: {family}.v1
  family: {family}
  version: v1
  kind: {kind}
  status: template          # change this once the node is filled in

project:
  name: "TODO"
  description: >-
    TODO: a concise public account of the mathematical content and principal results.
  authors: ["TODO"]
  license: "Apache-2.0"
  responsible_maintainers: ["TODO"]

repository:
  role: substantive-development

classification:
  arxiv: [math.NT]
  msc2020: ["11N05"]

conclusions:
  - id: replace_me
    declaration: {family}.v1.replace_me
    challenge: {family}.v1.challenge_replace_me
    imports: []
    # A conclusion may carry several justifications; exactly one is designated.
    justifications:
      - id: unjustified
        kind: none-yet
        note: >-
          TODO
    designated: unjustified

sources:
  - title: "TODO"
    authors: ["TODO"]
    type: "paper"            # paper | book | web discussion | folklore | original-proof | other
    id: "TODO"
    relationship: formalizes # formalizes | adapts | independently-proves | background | other
    note: >-
      TODO

automation:
  methods:
    - method: manual
      role: >-
        TODO

review:
  status: self-assessed
  reviewers: ["TODO"]

limitations:
  - >-
    TODO
"""


def register_in_umbrella(node_id: str, after: str | None = None) -> None:
    """Add a node's challenge to `IEANTN/Nodes.lean`, keeping the import list sorted."""
    umbrella = ROOT / "IEANTN" / "Nodes.lean"
    text = umbrella.read_text(encoding="utf-8")
    line = f"import IEANTN.Nodes.{node_id}.Challenge"
    if line in text:
        return
    lines = text.splitlines()
    imports = [i for i, entry in enumerate(lines) if entry.startswith("import ")]
    if not imports:
        return
    block = sorted(set(lines[imports[0]:imports[-1] + 1] + [line]))
    umbrella.write_text(
        "\n".join(lines[:imports[0]] + block + lines[imports[-1] + 1:]) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def new_node(family: str, kind: str) -> bool:
    """Scaffold a brand-new node at v1."""
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", family):
        print(f"error: `{family}` is not a usable Lean namespace component")
        return False
    target = NODES_DIR / family / "v1"
    if target.exists():
        print(f"error: {rel(target)} already exists (use `new-version {family}` instead)")
        return False

    target.mkdir(parents=True)
    (target / "Conclusions.lean").write_text(
        CONCLUSIONS_TEMPLATE.format(family=family), encoding="utf-8", newline="\n"
    )
    (target / "formalization.yaml").write_text(
        YAML_TEMPLATE.format(family=family, kind=kind), encoding="utf-8", newline="\n"
    )
    register_in_umbrella(f"{family}.v1")

    node = load_nodes()[f"{family}.v1"]
    (target / "Challenge.lean").write_text(
        render_challenge(f"{family}.v1", node), encoding="utf-8", newline="\n"
    )

    print(f"created {rel(target)}")
    print("\nnext:")
    print(f"  1. write the real conclusions in {rel(target / 'Conclusions.lean')}")
    print(f"  2. fill in {rel(target / 'formalization.yaml')} and change `node.status`")
    print("  3. python scripts/ieantn.py gen-challenges")
    print("  4. python scripts/ieantn.py check")
    print("\n`check-graph` will refuse this node until step 2 is done. That is deliberate.")
    return True


def new_version(family: str) -> bool:
    existing = versions_of(family)
    if not existing:
        print(f"error: no versions of `{family}` under {rel(NODES_DIR)}")
        return False
    latest_n, latest = existing[-1]
    new_n = latest_n + 1
    target = NODES_DIR / family / f"v{new_n}"
    if target.exists():
        print(f"error: {rel(target)} already exists")
        return False

    old_id, new_id = f"{family}.v{latest_n}", f"{family}.v{new_n}"
    target.mkdir(parents=True)
    for name in ("Conclusions.lean", "formalization.yaml"):
        text = (latest / name).read_text(encoding="utf-8")
        # Only this family's own version references may be bumped. A blanket `v1` -> `v2`
        # would also rewrite the *imported* nodes' versions, silently repointing the new node
        # at versions of its dependencies that may not exist.
        text = text.replace(old_id, new_id)
        (target / name).write_text(text, encoding="utf-8", newline="\n")

    metadata = target / "formalization.yaml"
    writer, data = edit_yaml(metadata)
    data["node"]["version"] = f"v{new_n}"
    data["node"]["status"] = "awaiting-solution"
    data["node"].pop("superseded_by", None)
    # The new version inherits none of the old one's evidence -- that is the point of branching.
    for conclusion in data.get("conclusions") or []:
        conclusion["justifications"] = [
            {
                "id": "unjustified",
                "kind": "none-yet",
                "note": f"Newly branched from {old_id}. Either bridge from it or justify directly.",
            }
        ]
        conclusion["designated"] = "unjustified"
    with metadata.open("w", encoding="utf-8", newline="\n") as handle:
        writer.dump(data, handle)

    register_in_umbrella(new_id)

    print(f"created {rel(target)} from {rel(latest)}")
    print("\nnext:")
    print(f"  1. edit {rel(target / 'Conclusions.lean')} -- this is the point of the new version")
    print("  2. python scripts/ieantn.py gen-challenges")
    print(f"  3. justify it: write a bridge from {old_id}, or a solution")
    print(f"  4. when {old_id} should retire: "
          f"python scripts/ieantn.py deprecate {old_id} --for {new_id}")
    return True


def deprecate(node_id: str, replacement: str) -> bool:
    nodes = load_nodes()
    if node_id not in nodes:
        print(f"error: unknown node `{node_id}`")
        return False
    if replacement not in nodes:
        print(f"error: unknown replacement node `{replacement}`")
        return False

    path = nodes[node_id]["_dir"] / "formalization.yaml"
    writer, data = edit_yaml(path)
    data["node"]["status"] = "deprecated"
    data["node"]["superseded_by"] = replacement
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        writer.dump(data, handle)
    print(f"marked {node_id} deprecated in favour of {replacement}")
    print("this changes nothing mechanically; it queues the migration and eventual deletion.")
    print("see: python scripts/ieantn.py housekeeping")
    return True


# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("check-closure", "check-graph", "report", "housekeeping", "status", "check"):
        sub.add_parser(name)
    generate = sub.add_parser("gen-challenges")
    generate.add_argument("--check", action="store_true", help="fail instead of rewriting")
    prints = sub.add_parser("fingerprint")
    prints.add_argument("--check", action="store_true", help="fail instead of rewriting")
    fresh = sub.add_parser("new-node")
    fresh.add_argument("family", help="e.g. FKS2")
    fresh.add_argument(
        "--kind", default="paper", choices=["paper", "pipeline", "folklore", "computation"]
    )
    version = sub.add_parser("new-version")
    version.add_argument("family", help="e.g. Lcm")
    written = sub.add_parser("record-receipt", help="verification workflow only")
    written.add_argument("conclusion")
    written.add_argument("--solution", required=True)
    written.add_argument("--run-url", default="")
    written.add_argument("--stamp", default="", help="timestamp; display only")
    retire = sub.add_parser("deprecate")
    retire.add_argument("node", help="e.g. Lcm.v1")
    retire.add_argument("--for", dest="replacement", required=True, help="e.g. Lcm.v2")

    args = parser.parse_args()
    if args.command == "check-closure":
        return 0 if check_closure() else 1
    if args.command == "check-graph":
        return 0 if check_graph() else 1
    if args.command == "gen-challenges":
        return 0 if gen_challenges(args.check) else 1
    if args.command == "fingerprint":
        return 0 if fingerprint(args.check) else 1
    if args.command == "report":
        return 0 if report() else 1
    if args.command == "status":
        return 0 if status() else 1
    if args.command == "record-receipt":
        return 0 if record_receipt(args.conclusion, args.solution, args.run_url, args.stamp) else 1
    if args.command == "housekeeping":
        return 0 if housekeeping() else 1
    if args.command == "new-node":
        return 0 if new_node(args.family, args.kind) else 1
    if args.command == "new-version":
        return 0 if new_version(args.family) else 1
    if args.command == "deprecate":
        return 0 if deprecate(args.node, args.replacement) else 1
    if args.command == "check":
        return 0 if all([check_closure(), check_graph(), gen_challenges(True)]) else 1
    return 2


if __name__ == "__main__":
    sys.exit(main())
