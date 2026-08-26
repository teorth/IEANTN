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
    python scripts/ieantn.py diff --base origin/main what this branch degrades, and for whom
    python scripts/ieantn.py housekeeping            the derived task queue
    python scripts/ieantn.py state                   refresh the committed STATE.md snapshot
    python scripts/ieantn.py check-receipts          every receipt names a real verification run
    python scripts/ieantn.py check                   every check, in --check mode

    python scripts/ieantn.py new-node FKS2           scaffold a brand-new node at v1
    python scripts/ieantn.py new-solution Lcm.v1     scaffold a solution project
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
import os
import pathlib
import re
import subprocess
import sys

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("error: PyYAML is required (pip install pyyaml)")

ROOT = pathlib.Path(__file__).resolve().parent.parent
NODES_DIR = ROOT / "IEANTN" / "Nodes"
VOCAB_DIR = ROOT / "IEANTN" / "Vocabulary"
#: Bridges live inside the library so the core build compiles them; see `check_bridges`.
BRIDGES_DIR = ROOT / "IEANTN" / "Bridges"
FINGERPRINTS = ROOT / "fingerprints.json"
STATE = ROOT / "STATE.md"
GRAPH = ROOT / "GRAPH.md"
PAGES = ROOT / "docs" / "nodes"
VERIFY_SCRIPT = ROOT / "scripts" / "verify-comparator.sh"
RECEIPTS = ROOT / "receipts"
CHANGES = ROOT / "changes"
SOLUTIONS = ROOT / "Solutions"

#: Where a spun-off Challenge says it came from.
REPOSITORY_URL = "https://github.com/teorth/IEANTN"

#: The four-line header every Lean file in this repository carries.
LICENCE_HEADER = (
    "/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: IEANTN contributors\n-/\n"
)

#: Toolchain minor releases behind current, past which a refresh is assumed to fall outside the
#: Mathlib cache window and cost many times the per-node budget. A heuristic, not a measurement.
CACHE_WINDOW_RELEASES = 2

#: Whether anyone has worked out what a conclusion assumes.
#:
#: An empty `imports` list is ambiguous on its own: it means either "this claim genuinely rests on
#: nothing else in the network" or "nobody has looked yet". Those are very different things to show
#: a reader, and the second is the normal state of a freshly cited result. `undetermined` is the
#: default precisely so that the honest state is the one you get without doing anything.
#:
#: `none` is the third case and is not the same as `identified` with an empty list: it says someone
#: looked and there is genuinely nothing upstream. Lcm.v2 assumes its prime-gap input internally by
#: design; MT's Theorem 1 is unconditional. Having a word for that keeps the check from emitting a
#: warning nobody can ever act on, which is how warnings stop being read.
IMPORT_STATUSES = {"identified", "none", "undetermined"}
DEFAULT_IMPORT_STATUS = "undetermined"


def import_status(conclusion: dict) -> str:
    """Whether this conclusion's imports have been worked out. Absent means not."""
    return conclusion.get("imports_status") or DEFAULT_IMPORT_STATUS


#: A justification that stands on its own evidence.
PRIMITIVE_KINDS = {"lean-comparator", "numerical", "literature", "asserted", "none-yet"}
#: A justification borrowed from another version via a proved bridge.
DERIVED_KINDS = {"bridged"}
JUSTIFICATION_KINDS = PRIMITIVE_KINDS | DERIVED_KINDS

#: Kinds meaning "checked by Lean in this repository". Everything else is a leaf of the trust
#: graph: something the network takes on faith, however reasonably.
VERIFIED_KINDS = {"lean-comparator"}

NODE_STATUSES = {
    "template",              # scaffolded, not yet filled in; refused by check-graph
    "stub",                  # conclusions stated, no solution intended yet
    "awaiting-solution",     # someone should write a solution
    "awaiting-verification",  # a complete solution exists, but no receipt yet
    "active",
    "deprecated",
}

IMPORT_RE = re.compile(r"^import\s+(\S+)", re.MULTILINE)

#: What may appear as a conclusion id, or as either half of an import reference. These strings are
#: interpolated verbatim into generated Lean, so anything not an identifier is either a typo or an
#: injection; there is no third case, and no reason to accept one.
LEAN_NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
LEAN_PATH_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_0-9][A-Za-z0-9_']*)*")


def _set_root(path: pathlib.Path) -> None:
    """Repoint every path global at `path`.

    For the tests, which run the real functions against a fixture repository rather than against
    this one. Nothing else should call it: the paths are derived from `__file__` precisely so that
    the tooling cannot be pointed somewhere unexpected by accident.
    """
    global ROOT, NODES_DIR, VOCAB_DIR, BRIDGES_DIR, FINGERPRINTS, STATE, GRAPH, PAGES, VERIFY_SCRIPT
    global RECEIPTS, CHANGES, SOLUTIONS
    ROOT = path
    NODES_DIR = ROOT / "IEANTN" / "Nodes"
    VOCAB_DIR = ROOT / "IEANTN" / "Vocabulary"
    BRIDGES_DIR = ROOT / "IEANTN" / "Bridges"
    PAGES = ROOT / "docs" / "nodes"
    FINGERPRINTS = ROOT / "fingerprints.json"
    STATE = ROOT / "STATE.md"
    GRAPH = ROOT / "GRAPH.md"
    VERIFY_SCRIPT = ROOT / "scripts" / "verify-comparator.sh"
    RECEIPTS = ROOT / "receipts"
    CHANGES = ROOT / "changes"
    SOLUTIONS = ROOT / "Solutions"
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


def under(module: str, root: str) -> bool:
    """Is `module` the module `root`, or one beneath it?

    `startswith` is not this test: it accepts `IEANTN.VocabularyScratch` as Vocabulary and
    `MathlibExtras` as Mathlib. Nothing has ever been named that way here, which is the problem --
    the check would go on passing on the day something was.
    """
    return module == root or module.startswith(root + ".")


def imports_of(path: pathlib.Path) -> list[str]:
    """Every module a Lean file imports.

    Comments are stripped first, and the module name is read up to whitespace rather than to end of
    line. Both matter, in opposite directions. Anchoring the old pattern at `$` meant
    `import Mathlib.Tactic -- why` matched nothing at all, so a trailing comment was enough to hide
    an import from every closure check -- silently, and in the direction that lets a violation
    through. Not stripping comments meant a commented-out import was reported as real.
    """
    return IMPORT_RE.findall(strip_lean_comments(path.read_text(encoding="utf-8")))


def strip_lean_comments(text: str) -> str:
    """Lean source with `--` line comments and nested `/- -/` blocks removed.

    Needed because a plain search for `sorry` also matches the word in prose. The docstring of an
    Examples file explaining *why* it may not contain `sorry` is not a `sorry`, and a check that
    cannot tell the difference is worse than none: it trains people to work around it.
    """
    out: list[str] = []
    index, depth, length = 0, 0, len(text)
    while index < length:
        if text.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and text.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth:
            index += 1
        elif text.startswith("--", index):
            newline = text.find("\n", index)
            index = length if newline < 0 else newline
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


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


def bridge_sources(justification: dict) -> list[str]:
    """The conclusions a `bridged` justification borrows from.

    `from` may name one conclusion or several. Several is the case where a node was temporarily
    split so that separate groups could work on its parts in parallel, and is later sewn back
    together: `Dusart_part_1.v1.main` and `Dusart_part_2.v1.main` together imply `Dusart.v3.main`.
    So a bridge is not only a relation between versions of one family -- it is many-to-one, and may
    cross families.
    """
    source = justification.get("from")
    if source is None:
        return []
    if isinstance(source, str):
        return [source]
    return [str(entry) for entry in source]


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


def check_pins() -> bool:
    """The verification toolchain's pins must match this repository's Lean toolchain.

    `lean4export` has to be built with the same Lean as the code it exports, so bumping
    `lean-toolchain` silently invalidates the pin in `verify-comparator.sh`. That script catches it
    — but only when someone next runs a verification, which may be weeks later, and which will look
    like the verification is broken rather than like the bump was incomplete. Checking here makes
    the *bump* red, which is when the fix is obvious and cheap.
    """
    problems = Problems()
    if not VERIFY_SCRIPT.is_file():
        return problems.report("verification pins")
    declared = re.search(
        r"^lean4export_toolchain=(\S+)", VERIFY_SCRIPT.read_text(encoding="utf-8"), re.MULTILINE
    )
    if declared is None:
        problems.add(
            rel(VERIFY_SCRIPT),
            "declares no `lean4export_toolchain=`, so nothing can check its pin against this "
            "repository's toolchain",
        )
    else:
        current = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
        if declared.group(1) != current:
            problems.add(
                rel(VERIFY_SCRIPT),
                f"pins lean4export for `{declared.group(1)}` but this repository is on "
                f"`{current}`. Update `lean4export_commit` to the tag matching the new toolchain, "
                "and re-check that Comparator and NanoDa still understand the export format.",
            )
    return problems.report("verification pins")


RUN_URL_RE = re.compile(r"^https://github\.com/([^/]+/[^/]+)/actions/runs/(\d+)$")


def check_receipts(online: bool = True) -> bool:
    """Every receipt must point at a real, successful run of the verification workflow.

    This exists because the intended enforcement is impossible here. The plan was a ruleset
    restricting `receipts/` to the verification workflow's identity; GitHub refuses push rulesets on
    a public repository and on any repository not owned by an organisation, and separately refuses
    to make the Actions app a bypass actor outside an organisation. So there is no path rule to be
    had.

    Checking provenance turns out to be the better control regardless. A path rule says *who wrote
    the file*; this says *that the verification actually happened*, which is the thing anyone
    forging a receipt would have to fake. A commit author is trivially forged locally; a successful
    run of `verify.yml` in this repository is not, because it needs a maintainer to approve the
    `verification` environment.

    Offline this checks only the shape of the recorded URL, so it stays useful without network
    access; CI runs it online.
    """
    problems = Problems()
    remote = subprocess.run(
        ["git", "remote", "get-url", "origin"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
    ).stdout.strip()
    expected = re.sub(r"^.*github\.com[:/]|\.git$", "", remote) if remote else None
    seen_runs: dict[str, str] = {}

    # Everything below rests on the receipt naming a run in *this* repository: anyone can stand up
    # a repository with a workflow called `verify.yml` whose jobs succeed. So when the check is
    # online and cannot tell which repository this is, it must refuse rather than go and ask the
    # one the receipt names -- which is what it used to do, making the whole check bypassable by
    # deleting a git remote.
    if online and expected is None and RECEIPTS.is_dir() and any(RECEIPTS.glob("*.json")):
        problems.add(
            rel(RECEIPTS),
            "cannot determine this repository from `git remote get-url origin`, so a receipt's "
            "recorded run cannot be checked against it. Refusing rather than trusting the "
            "repository the receipt names.",
        )
        return problems.report("receipt provenance")

    for path in sorted(RECEIPTS.glob("*.json")) if RECEIPTS.is_dir() else []:
        receipt = json.loads(path.read_text(encoding="utf-8"))
        url = (receipt.get("run") or {}).get("workflow_run", "")
        match = RUN_URL_RE.match(url)
        if match is None:
            problems.add(rel(path), f"records no usable workflow run (`{url}`)")
            continue
        repository, run_id = match.group(1), match.group(2)
        if expected and repository != expected:
            problems.add(rel(path), f"points at `{repository}`, not `{expected}`")
            continue
        # One run, one node. Without this, a receipt for any node validated against any successful
        # verification: copying the run URL out of a real receipt into a fabricated one passed.
        # Uniqueness is the part that works retroactively; the job-name check below is the sharper
        # one, and applies to every run recorded since the node went into the job name.
        node_of = str(receipt.get("conclusion") or path.stem).rsplit(".", 1)[0]
        claimed = seen_runs.setdefault(url, node_of)
        if claimed != node_of:
            problems.add(
                rel(path),
                f"cites run {run_id}, which another receipt already cites for `{claimed}`. One "
                "verification run covers one node.",
            )

        if not online:
            continue
        finished = subprocess.run(
            ["gh", "api", f"repos/{repository}/actions/runs/{run_id}",
             "--jq", "[.conclusion, .path] | @tsv"],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        )
        if finished.returncode != 0:
            problems.add(rel(path), f"run {run_id} could not be read: {finished.stderr.strip()}")
            continue
        parts = finished.stdout.strip().split("\t")
        conclusion, workflow = (parts + ["", ""])[:2]
        if conclusion != "success":
            problems.add(rel(path), f"run {run_id} concluded `{conclusion}`, not `success`")
        if workflow != ".github/workflows/verify.yml":
            problems.add(rel(path), f"run {run_id} is `{workflow}`, not the verification workflow")
            continue

        # `verify.yml` puts the dispatched node in its job names, so GitHub's record of the run
        # says which node was verified -- independently of anything the receipt asserts. Runs from
        # before that convention have no parenthesised job name; those fall back to the uniqueness
        # check above rather than failing, since re-running them is not possible.
        jobs = subprocess.run(
            ["gh", "api", f"repos/{repository}/actions/runs/{run_id}/jobs",
             "--jq", ".jobs[].name"],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        )
        names = jobs.stdout.split("\n") if jobs.returncode == 0 else []
        if any("(" in name for name in names) and not any(f"({node_of})" in name for name in names):
            problems.add(
                rel(path),
                f"run {run_id} verified {[n for n in names if '(' in n]}, not `{node_of}`",
            )

    return problems.report("receipt provenance")


def check_closure() -> bool:
    """Vocabulary and Conclusions may not reach outside Mathlib.

    This is the invariant the architecture rests on: a challenge transitively imports Vocabulary,
    so if Vocabulary reached outside Mathlib no node could be spun off as a standalone Palomar
    submission. See docs/ARCHITECTURE.md section 2.
    """
    problems = Problems()

    for path in sorted(VOCAB_DIR.rglob("*.lean")):
        for module in imports_of(path):
            if not (under(module, "Mathlib") or under(module, "IEANTN.Vocabulary")):
                problems.add(rel(path), f"Vocabulary may import only Mathlib; found `{module}`")

    for directory in node_dirs():
        conclusions = directory / "Conclusions.lean"
        if conclusions.is_file():
            for module in imports_of(conclusions):
                ok = (
                    under(module, "Mathlib")
                    or under(module, "IEANTN.Vocabulary")
                    or (under(module, "IEANTN.Nodes") and module.endswith(".Conclusions"))
                    # Any node's `Tables`, not only this node's. A table is data, and the node that
                    # computed it is not always the node that states a claim about it -- FKS2's
                    # pipelines are stated in terms of quantities BKLNW tabulates. Restricting
                    # tables to their own node would force a copy, and a copied table is a second
                    # source of truth.
                    or (under(module, "IEANTN.Nodes") and module.endswith(".Tables"))
                )
                if not ok:
                    problems.add(
                        rel(conclusions),
                        "a Conclusions file may import only Mathlib, Vocabulary, other "
                        f"Conclusions and any node's Tables; found `{module}`",
                    )
        # A node may carry `Examples.lean`: consequences drawn from its conclusions, to show what
        # the node actually buys. They make no claims of record, so they are not fingerprinted --
        # but they must not import the node's *Challenge*, which is sorried. An example built on a
        # `sorry` demonstrates nothing, and would look exactly like one that demonstrates
        # something.
        examples = directory / "Examples.lean"
        if examples.is_file():
            for module in imports_of(examples):
                ok = (
                    under(module, "Mathlib")
                    or under(module, "IEANTN.Vocabulary")
                    or (under(module, "IEANTN.Nodes") and module.endswith(".Conclusions"))
                )
                if not ok:
                    problems.add(
                        rel(examples),
                        f"an Examples file may import only Mathlib, Vocabulary and Conclusions; "
                        f"found `{module}`"
                        + (
                            " -- importing a Challenge would let an example rest on its `sorry`"
                            if module.endswith(".Challenge")
                            else ""
                        ),
                    )
            code = strip_lean_comments(examples.read_text(encoding="utf-8"))
            if re.search(r"\bsorry\b", code):
                problems.add(
                    rel(examples),
                    "an Examples file may not contain `sorry`: an example with a hole in it "
                    "demonstrates nothing, while looking exactly like one that does.",
                )

    # A bridge proves that one node's conclusion follows from others'. It carries trust, so it is
    # held to the same closure rule as a Conclusions file and, unlike a solution, it is compiled by
    # the ordinary core build -- an uncompiled bridge would attest nothing while looking like it
    # attested something. Hence no `sorry`, and no import of a Challenge: a bridge resting on the
    # very `sorry` it is supposed to discharge is the one failure mode worth designing out.
    for path in sorted(BRIDGES_DIR.rglob("*.lean")):
        for module in imports_of(path):
            ok = (
                under(module, "Mathlib")
                or under(module, "IEANTN.Vocabulary")
                or (under(module, "IEANTN.Nodes") and module.endswith(".Conclusions"))
                or under(module, "IEANTN.Bridges")
            )
            if not ok:
                problems.add(
                    rel(path),
                    "a bridge may import only Mathlib, Vocabulary, Conclusions and other bridges; "
                    f"found `{module}`"
                    + (
                        " -- a bridge that imports a Challenge would rest on the `sorry` it exists "
                        "to discharge"
                        if module.endswith(".Challenge")
                        else ""
                    ),
                )
        if re.search(r"\bsorry\b", strip_lean_comments(path.read_text(encoding="utf-8"))):
            problems.add(
                rel(path),
                "a bridge may not contain `sorry`: it is the proof that transports trust between "
                "versions, so a hole in it silently launders an unproved claim into a justified one.",
            )

    for directory in node_dirs():
        # `Tables.lean` is the optional home for a paper's bulk data -- the numeric tables and
        # parameter sets that some explicit results are stated against. It exists so that
        # `Conclusions.lean` stays the short file a human audits: a reviewer checking three claims
        # should not have to scroll past two hundred rows to reach them.
        #
        # Pure data, so no theorems: a *statement* about a table belongs in Conclusions, where it
        # becomes a claim of record with a fingerprint, and a *proof* about one belongs in a
        # solution. Held to the same import closure as Conclusions for the usual reason -- a
        # challenge transitively imports this, so anything it reaches must be spin-off-able.
        tables = directory / "Tables.lean"
        if tables.is_file():
            for module in imports_of(tables):
                ok = (
                    under(module, "Mathlib")
                    or under(module, "IEANTN.Vocabulary")
                    or (under(module, "IEANTN.Nodes") and module.endswith(".Tables"))
                )
                if not ok:
                    problems.add(
                        rel(tables),
                        "a Tables file may import only Mathlib, Vocabulary and other Tables; "
                        f"found `{module}`. Keep the import list short -- a table that needs a "
                        "conclusion to state it is not data.",
                    )
            code = strip_lean_comments(tables.read_text(encoding="utf-8"))
            for keyword in ("theorem", "lemma"):
                if re.search(rf"\b{keyword}\s", code):
                    problems.add(
                        rel(tables),
                        f"a Tables file may not declare a `{keyword}`: it holds data, not claims. "
                        "A statement about a table is a conclusion; a proof about one belongs in a "
                        "solution.",
                    )
            if re.search(r"\bsorry\b", code):
                problems.add(rel(tables), "a Tables file may not contain `sorry`")

        challenge = directory / "Challenge.lean"
        if challenge.is_file():
            for module in imports_of(challenge):
                if not (under(module, "IEANTN.Nodes") and module.endswith(".Conclusions")):
                    problems.add(
                        rel(challenge),
                        f"a Challenge file may import only Conclusions files; found `{module}`",
                    )

    # A solution takes the core as a path dependency, and Lake builds a path dependency with the
    # *root* project's toolchain, so a solution pinning a *different* Lean than the repository
    # either gets ignored or tries to build the core under the wrong compiler.
    #
    # The first version of this check concluded that solutions should therefore carry no
    # `lean-toolchain` at all. That was wrong, and local iteration caught it: Mathlib's `cache`
    # executable reads `lean-toolchain` from the project it runs in, so a solution without one
    # cannot fetch its Mathlib from cache -- which is the difference between a one-minute step and
    # an hour of compiling. The right rule is equality, not absence.
    root_toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    for directory in sorted(SOLUTIONS.iterdir()) if SOLUTIONS.is_dir() else []:
        if not (directory / "lakefile.toml").is_file():
            continue
        toolchain = directory / "lean-toolchain"
        if not toolchain.is_file():
            problems.add(
                rel(directory),
                "a solution needs its own `lean-toolchain`, matching the repository's: Mathlib's "
                "`cache` tool reads it from the project directory, and without it the solution "
                "compiles Mathlib from source instead of fetching it.",
            )
        elif toolchain.read_text(encoding="utf-8").strip() != root_toolchain:
            problems.add(
                rel(toolchain),
                f"pins `{toolchain.read_text(encoding='utf-8').strip()}` but the repository is on "
                f"`{root_toolchain}`. A solution takes the core as a path dependency, so a "
                "divergent pin cannot work; what pins a verification is the commit its receipt "
                "records.",
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

    every_conclusion = {
        f"{other_id}.{c.get('id')}"
        for other_id, other in nodes.items()
        for c in conclusions_of(other)
    }

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

            # `cid` is interpolated into the generated Challenge as a declaration name. Nothing
            # downstream re-reads that file critically -- CI only diffs it against what the
            # generator produces, so text smuggled in through the metadata would be regenerated
            # faithfully and compiled into the core library. An id is an identifier or it is
            # wrong.
            if not LEAN_NAME_RE.fullmatch(str(cid)):
                problems.add(
                    where,
                    f"conclusion id `{cid}` is not a Lean identifier. It is written into the "
                    "generated challenge as a declaration name, so it may contain only letters, "
                    "digits, underscores and primes, and may not begin with a digit.",
                )

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
                    sources = bridge_sources(justification)
                    if not sources:
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: `bridged` must name "
                            "`from` (one conclusion, or several)",
                        )
                    for source in sources:
                        if source not in every_conclusion:
                            problems.add(
                                where,
                                f"conclusion `{cid}`, justification `{jid}`: bridges from "
                                f"`{source}`, which does not exist",
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
                    elif not justification["bridge"].startswith("IEANTN/Bridges/"):
                        # A bridge outside the library is never compiled, so it would keep
                        # justifying its target after either statement moved out from under it.
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: bridge file "
                            f"`{justification['bridge']}` must live under `IEANTN/Bridges/` so "
                            "that the core build compiles it; a bridge nothing builds attests "
                            "nothing",
                        )

            if available and designated_of(conclusion) is None:
                problems.add(
                    where,
                    f"conclusion `{cid}`: `designated` is `{conclusion.get('designated')}`, which "
                    f"is not one of its justification ids ({sorted(seen_ids)})",
                )
            # A receipt with nothing designating it means a verification happened and the graph
            # does not know. That is how the first real verification landed: the workflow wrote
            # the receipt, the metadata still said `none-yet`, and `status` reported the node as
            # unverified. A warning rather than an error, because the window between the workflow's
            # commit and the pull request that designates it is legitimate.
            # `designated_kind`, not the `kind` left over from the loop above: a conclusion may
            # carry justifications after the designated one, and reading the last one iterated
            # reported the wrong kind the moment a second ground was recorded.
            settled = designated_kind(conclusion)
            if load_receipt(f"{node_id}.{cid}") is not None and settled != "lean-comparator":
                problems.warn(
                    where,
                    f"conclusion `{cid}` has a receipt but designates `{settled}`. A verification "
                    "was recorded and nothing points at it; add a `lean-comparator` justification "
                    "and designate it.",
                )

            status = conclusion.get("imports_status")
            if status is not None and status not in IMPORT_STATUSES:
                problems.add(
                    where,
                    f"conclusion `{cid}`: imports_status `{status}` is not one of "
                    + ", ".join(sorted(IMPORT_STATUSES)),
                )
            if status == "identified" and not (conclusion.get("imports") or []):
                problems.add(
                    where,
                    f"conclusion `{cid}`: `imports_status: identified` but no imports are listed. "
                    "If someone looked and there are genuinely none, say `none`; if nobody has "
                    "looked, drop the field and let it read as undetermined.",
                )
            if status == "none" and (conclusion.get("imports") or []):
                problems.add(
                    where,
                    f"conclusion `{cid}`: `imports_status: none` but imports are listed.",
                )

            issue = conclusion.get("issue")
            if issue is not None and not isinstance(issue, int):
                problems.add(where, f"conclusion `{cid}`: `issue` must be a number, not `{issue}`")
            elif designated_kind(conclusion) == "none-yet" and issue is None:
                problems.warn(
                    where,
                    f"conclusion `{cid}` is unjustified and names no `issue`: nobody can claim "
                    "work nobody can find. Open an issue and record its number.",
                )

            if designated_kind(conclusion) == "none-yet" and len(available) > 1:
                problems.warn(
                    where,
                    f"conclusion `{cid}` designates a `none-yet` justification while others are "
                    "available; designate one of those instead",
                )

            for dependency in conclusion.get("imports") or []:
                target_node = dependency.get("node")
                target_conclusion = dependency.get("conclusion")
                # Both halves become part of a hypothesis binder's type in the generated
                # challenge, so they are subject to the same rule as a conclusion id. Checked
                # before the existence test below, which would otherwise report a crafted string
                # as a mere unknown node.
                for label, value, pattern in (
                    ("node", target_node, LEAN_PATH_RE),
                    ("conclusion", target_conclusion, LEAN_NAME_RE),
                ):
                    if not pattern.fullmatch(str(value)):
                        problems.add(
                            where,
                            f"conclusion `{cid}`: import {label} `{value}` is not a Lean name, and "
                            "is written verbatim into the generated challenge",
                        )
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
                bridge_sources(justification) if justification.get("kind") == "bridged" else []
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


def render_bridges_umbrella() -> str:
    """`IEANTN/Bridges.lean`, importing every bridge.

    Bridges are compiled by the core build for the reason given in `check_closure`: one that is
    merely present at a recorded path has never been checked against the statements it claims to
    relate, and would keep passing after either of them moved.
    """
    modules = sorted(
        "IEANTN.Bridges." + ".".join(path.relative_to(BRIDGES_DIR).with_suffix("").parts)
        for path in BRIDGES_DIR.rglob("*.lean")
    )
    return (
        "/-\n"
        "Copyright (c) 2026 IEANTN contributors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: Terence Tao\n"
        "-/\n"
        + "".join(f"import {module}\n" for module in modules)
        + """
/-!
# Bridges

**Generated file - do not edit.**  Regenerated by `python scripts/ieantn.py gen-challenges`.

Each bridge proves that one node's conclusion follows from others', and is recorded as a `bridged`
justification in the target node's `formalization.yaml`. Bridges sit outside the import graph on
purpose -- see docs/ARCHITECTURE.md section 4.
-/
"""
    )


def render_umbrella(nodes: dict[str, dict]) -> str:
    """`IEANTN/Nodes.lean`, importing every node's challenge and examples.

    Generated rather than hand-maintained: it drifted three times during development, each time
    silently, because a missing import only shows up as a module that quietly is not built.
    """
    modules = []
    for node_id, node in sorted(nodes.items()):
        # Tables before the challenge, and listed even though `Conclusions` usually imports them:
        # a table no conclusion mentions yet is still data of record, and leaving it out of the
        # umbrella would mean nothing compiled it.
        if (node["_dir"] / "Tables.lean").is_file():
            modules.append(f"IEANTN.Nodes.{node_id}.Tables")
        modules.append(f"IEANTN.Nodes.{node_id}.Challenge")
        if (node["_dir"] / "Examples.lean").is_file():
            modules.append(f"IEANTN.Nodes.{node_id}.Examples")
    return (
        "/-\n"
        "Copyright (c) 2026 IEANTN contributors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: Terence Tao\n"
        "-/\n"
        + "".join(f"import {module}\n" for module in modules)
        + """
/-!
# The node network

**Generated file - do not edit.**  Regenerated by `python scripts/ieantn.py gen-challenges`.

Every node version's conclusions, generated challenge, and examples where present. Nodes are
versioned: a node lives at `IEANTN/Nodes/<Family>/<version>/` and its id is `<Family>.<version>`.
-/
"""
    )


def gen_challenges(check_only: bool) -> bool:
    problems = Problems()
    nodes = load_nodes()
    outputs = [(node["_dir"] / "Challenge.lean", render_challenge(node_id, node))
               for node_id, node in nodes.items()]
    outputs.append((ROOT / "IEANTN" / "Nodes.lean", render_umbrella(nodes)))
    if BRIDGES_DIR.is_dir():
        outputs.append((ROOT / "IEANTN" / "Bridges.lean", render_bridges_umbrella()))
    for path, rendered in outputs:
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


def verification_tools() -> dict[str, str]:
    """The pinned revisions of the four tools a verification actually trusts.

    Read out of `verify-comparator.sh` rather than duplicated, so they cannot drift apart. Recording
    them is what makes "re-run at the recorded pin" (ARCHITECTURE section 4) a defined operation
    rather than a phrase: without them a receipt says a verification happened but not what checked
    it, and a later Comparator or NanoDa is a different verifier.
    """
    if not VERIFY_SCRIPT.is_file():
        return {}
    text = VERIFY_SCRIPT.read_text(encoding="utf-8")
    found = {}
    for tool in ("comparator", "lean4export", "landrun", "nanoda"):
        match = re.search(rf"^{tool}_commit=(\S+)", text, re.MULTILINE)
        if match:
            found[tool] = match.group(1)
    return found


def repository_commit() -> str | None:
    """The commit a verification ran against, if this is a git checkout.

    The receipt's own pin: re-running means checking this out, where the core and the solution agree
    by construction. Without it the receipt names a workflow run and a set of statements but not the
    tree they were verified in.
    """
    finished = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
    )
    return finished.stdout.strip() or None if finished.returncode == 0 else None


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
    """How many Lean minor releases apart two toolchain strings are, if it can be told.

    Compares `(major, minor)` pairs, not minor alone: `v4.34` to `v5.2` is not thirty-two releases
    apart. A differing major version is reported as beyond the cache window, since it certainly is.
    Returns None when either string is unrecognisable, so the caller falls back to the
    undifferentiated "stale" verdict rather than inventing a number.
    """
    pattern = re.compile(r"v(\d+)\.(\d+)")
    left, right = pattern.search(recorded or ""), pattern.search(current or "")
    if not left or not right:
        return None
    old_major, old_minor = int(left.group(1)), int(left.group(2))
    new_major, new_minor = int(right.group(1)), int(right.group(2))
    if old_major != new_major:
        return CACHE_WINDOW_RELEASES + 1
    return abs(new_minor - old_minor)


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


def solution_drift(receipt: dict) -> str | None:
    """Whether the solution has been edited since the verification that attested to it.

    `assess` compares statement fingerprints, so it catches a *statement* moving out from under a
    receipt. Nothing caught the *solution* moving. The receipt says Comparator accepted that
    solution, and after an edit it has accepted something else -- possibly a comment, possibly not,
    and the receipt cannot tell you which.

    Reported rather than fatal, because the common case really is a comment. What makes it
    detectable at all is `repository.commit`, which schema 2 records and schema 1 does not; older
    receipts are skipped rather than guessed at. A commit that is not present locally -- a shallow
    clone, or one written on a branch since deleted -- is also skipped.
    """
    commit = (receipt.get("repository") or {}).get("commit")
    project = (receipt.get("solution") or {}).get("project")
    if not commit or not project:
        return None
    known = subprocess.run(
        ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if known.returncode != 0:
        return None
    changed = subprocess.run(
        ["git", "diff", "--name-only", commit, "--", project],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if changed.returncode != 0:
        return None
    files = [line for line in changed.stdout.splitlines() if line.strip()]
    if not files:
        return None
    return (f"{project} has changed in {len(files)} file(s) since the verification at "
            f"{commit[:12]}; the receipt attests to that commit, not to what is there now")


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
            drift = solution_drift(receipt)
            if drift is not None:
                print(f"          note: {drift}")

    print("\n" + "=" * 78)
    print(
        "  ".join(f"{name}: {count}" for name, count in lights.items() if count)
        or "  nothing recorded"
    )
    if lights["BROKEN"]:
        print("\nA BROKEN receipt is not staleness: the verified implication no longer connects")
        print("to what the node now claims. Re-verify, or make a new version.")
    return True


def new_solution(node_id: str) -> bool:
    """Scaffold `Solutions/<node>/` as its own Lake project.

    A solution is a separate Lake project so its dependencies stay its own: a proof needing PNT+ or
    LeanCert must not force those on the core, which has to stay Mathlib-only and fast. It takes
    the core as a path dependency in order to see the node's `Conclusions`.

    It deliberately does *not* import the node's `Challenge`: Comparator compares two modules
    declaring the same names, so importing it would collide.
    """
    nodes = load_nodes()
    if node_id not in nodes:
        print(f"error: unknown node `{node_id}`")
        return False
    target = SOLUTIONS / node_id
    if target.exists():
        print(f"error: {rel(target)} already exists")
        return False

    conclusions = conclusions_of(nodes[node_id])
    theorems = [f"{node_id}.challenge_{c.get('id')}" for c in conclusions]
    target.mkdir(parents=True)

    (target / "lakefile.toml").write_text(
        f'name = "solution_{node_id.replace(".", "_")}"\n'
        'defaultTargets = ["Solution"]\n\n'
        "# The core library, for the node's `Conclusions`. Add whatever else the proof needs --\n"
        "# PNT+, LeanCert, PrimeCert -- here rather than in the core lakefile.\n"
        "[[require]]\n"
        'name = "IEANTN"\n'
        'path = "../.."\n\n'
        "[[lean_lib]]\n"
        'name = "Solution"\n'
        'roots = ["Solution"]\n',
        encoding="utf-8",
        newline="\n",
    )

    body = []
    for conclusion in conclusions:
        cid = conclusion.get("id")
        imports = conclusion.get("imports") or []
        binder = "".join(
            f"\n    ({hypothesis_name(d)} : {d.get('node')}.{d.get('conclusion')})" for d in imports
        )
        if binder:
            body.append(f"theorem {node_id}.challenge_{cid}{binder} :\n    {node_id}.{cid} := by")
        else:
            body.append(f"theorem {node_id}.challenge_{cid} : {node_id}.{cid} := by")
        body.append("  sorry\n")

    needed = sorted(
        {module_of(node_id)}
        | {module_of(str(d.get("node"))) for c in conclusions for d in (c.get("imports") or [])}
    )
    (target / "Solution.lean").write_text(
        "/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\nAuthors: TODO\n-/\n"
        + "".join(f"import {module}\n" for module in needed)
        + f"""
/-!
# Solution: `{node_id}`

Proves the same declarations `Challenge.lean` states. Do **not** import the challenge module --
Comparator compares two modules declaring the same names, so importing it would collide.

This file may import anything. It is not part of the core build, and it is verified once and then
left alone; readability is not a goal here.

Replace each `sorry` below. While any remain, record progress in the node's `formalization.yaml`
under `progress`, and leave the justification alone -- an incomplete solution justifies nothing.
-/

"""
        + "\n".join(body),
        encoding="utf-8",
        newline="\n",
    )

    (target / "comparator.json").write_text(
        json.dumps(
            {
                "challenge_module": f"IEANTN.Nodes.{node_id}.Challenge",
                "solution_module": "Solution",
                "theorem_names": theorems,
                "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                "enable_nanoda": True,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )

    print(f"created {rel(target)}")
    print("\nnext:")
    print(f"  1. prove the {len(theorems)} declaration(s) in {rel(target / 'Solution.lean')}")
    print(f"  2. cd {rel(target)} && lake build")
    print("  3. ask a maintainer to run the `Verify a solution` workflow for this node")
    print("\nDo not edit the justification or write a receipt yourself: receipts are written by")
    print("the verification workflow, and one you can write attests nothing.")
    return True


def _comparator_covers_every_conclusion(node_id: str, node: dict) -> bool:
    """Refuse to receipt conclusions Comparator was never asked about.

    A receipt is written per conclusion, but Comparator is run once per *node*, against the
    `theorem_names` listed in the solution's `comparator.json`. Nothing previously connected the
    two, so a node whose conclusions had grown since its solution was written would receive a
    receipt for the new conclusion as well -- a full `lean-comparator` justification for a
    statement no verifier had ever seen. That is the one failure this whole apparatus exists to
    prevent, and it needed no adversary: adding a second conclusion to a verified node was enough.
    """
    config = SOLUTIONS / node_id / "comparator.json"
    where = rel(config)
    if not config.is_file():
        print(f"error: {where} does not exist, so nothing says what was verified")
        return False
    try:
        listed = set(json.loads(config.read_text(encoding="utf-8")).get("theorem_names") or [])
    except json.JSONDecodeError as broken:
        print(f"error: {where} is not readable JSON: {broken}")
        return False

    expected = {f"{node_id}.challenge_{c.get('id')}" for c in conclusions_of(node)}
    unverified = sorted(expected - listed)
    if unverified:
        print(
            f"error: {where} does not list {', '.join(unverified)}.\n"
            "       Comparator was not asked about "
            f"{'them' if len(unverified) > 1 else 'it'}, so no receipt may claim "
            f"{'they were' if len(unverified) > 1 else 'it was'} verified. Add "
            f"{'them' if len(unverified) > 1 else 'it'} to the solution and re-run the "
            "verification."
        )
        return False
    # The converse is a mistake rather than a hazard -- a name that no longer corresponds to a
    # conclusion was probably renamed, and the receipt would be recorded under the new name while
    # Comparator checked the old one.
    for stale in sorted(listed - expected):
        print(f"warning: {where} lists `{stale}`, which is not a conclusion of {node_id}")
    return True


def record_receipt(node_id: str, solution: str, run_url: str, stamp: str) -> bool:
    """Write a receipt. **Run by the verification workflow, never by an author.**

    An author-written receipt is worth nothing -- it is a claim of verification typed by the person
    making the claim. What makes a receipt mean something is not this function refusing to run: it
    is that `check-receipts` fetches the run it names and requires a successful run of `verify.yml`
    for this node, which needs a maintainer to approve the `verification` environment. (The
    intended `receipts/` path ruleset is not available -- GitHub refuses push rules on public
    repositories and on repositories outside an organisation. Provenance replaced it.)
    """
    nodes = load_nodes()
    if node_id not in nodes:
        print(f"error: unknown node `{node_id}`")
        return False

    if not _comparator_covers_every_conclusion(node_id, nodes[node_id]):
        return False

    fingerprints = compute_fingerprints()
    RECEIPTS.mkdir(exist_ok=True)
    for conclusion in conclusions_of(nodes[node_id]):
        key = f"{node_id}.{conclusion.get('id')}"
        wanted = [key] + [
            f"{d.get('node')}.{d.get('conclusion')}" for d in (conclusion.get("imports") or [])
        ]
        missing = [name for name in wanted if name not in fingerprints]
        if missing:
            print(f"error: no fingerprint for {missing}")
            return False
        receipt = {
            "schema": 2,
            "conclusion": key,
            "challenge": conclusion.get("challenge"),
            "statement": {name: fingerprints[name] for name in wanted},
            "environment": current_environment(),
            "repository": {"commit": repository_commit()},
            "tools": verification_tools(),
            "solution": {"project": solution},
            "run": {"workflow_run": run_url, "recorded_at": stamp},
        }
        path = receipt_path(key)
        path.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
        )
        print(f"wrote {rel(path)}")

    designate_verification(node_id, run_url)
    return True


def designate_verification(node_id: str, run_url: str) -> None:
    """Record the verification as the node's designated justification.

    A Lean-verified justification dominates the alternatives: it rests on no citation, no external
    computation and no other version, so once a verification exists it is almost always the right
    thing to point at. Designating it here rather than leaving it to a later pull request avoids the
    state the first real verification landed in -- a receipt written, the metadata still saying
    `none-yet`, and `status` reporting a node unverified moments after verifying it.

    A maintainer can still re-designate afterwards; that is an ordinary reviewed edit. What should
    not happen is the graph silently disagreeing with the receipts.
    """
    metadata = NODES_DIR / pathlib.PurePosixPath(node_id.replace(".", "/")) / "formalization.yaml"
    writer, data = edit_yaml(metadata)
    for conclusion in data.get("conclusions") or []:
        justifications = conclusion.setdefault("justifications", [])
        existing = next(
            (j for j in justifications if j.get("kind") == "lean-comparator"), None
        )
        if existing is None:
            existing = {
                "id": "comparator",
                "kind": "lean-comparator",
                "note": f"Comparator accepted the solution. Run: {run_url}",
            }
            justifications.append(existing)
        else:
            # Re-verification: the receipt now names the new run, and a note still naming the old
            # one sends a reader to a run that verified a statement this one may have replaced.
            existing["note"] = f"Comparator accepted the solution. Run: {run_url}"
        conclusion["designated"] = existing["id"]
        conclusion.pop("progress", None)
    # Not an unconditional `active`: verifying a deprecated node is a legitimate thing to do --
    # keeping an old version green while dependants migrate off it is exactly the case -- and
    # flipping its status here would silently un-deprecate it, dropping it out of the migration
    # queue that `housekeeping` derives.
    meta = data.setdefault("node", {})
    if meta.get("status") != "deprecated":
        meta["status"] = "active"
    with metadata.open("w", encoding="utf-8", newline="\n") as handle:
        writer.dump(data, handle)
    print(f"designated the verification in {rel(metadata)}")


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
            for source in bridge_sources(justification):
                result |= leaves(source, seen)
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


def closed_issues(numbers: set[int]) -> set[int]:
    """Which of these issue numbers are closed, as far as `gh` can tell.

    Best-effort and silent on failure: `gh` may be absent, unauthenticated, or offline, and
    housekeeping has to stay useful without it. An issue that cannot be read is treated as open,
    because reporting live work as abandoned is the more expensive mistake.
    """
    closed: set[int] = set()
    for number in sorted(numbers):
        finished = subprocess.run(
            ["gh", "issue", "view", str(number), "--json", "state", "--jq", ".state"],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        )
        if finished.returncode == 0 and finished.stdout.strip().upper() == "CLOSED":
            closed.add(number)
    return closed


def housekeeping() -> bool:
    """The task queue, derived from graph state rather than maintained by hand."""
    nodes = load_nodes()
    importers = importers_of(nodes)
    tasks: list[str] = []

    # An outstanding conclusion whose issue has been closed is work nobody is tracking any more:
    # the queue says it is claimed, and the issue tracker says it is finished. It happens by
    # accident -- closing the issue alongside the pull request that created the node rather than
    # the one that justifies it -- and nothing else in the tooling would ever mention it again.
    outstanding = {
        conclusion.get("issue")
        for node in nodes.values()
        for conclusion in conclusions_of(node)
        if designated_kind(conclusion) in {"none-yet", "literature", "asserted"}
        and isinstance(conclusion.get("issue"), int)
    }
    stale_issues = closed_issues({n for n in outstanding if isinstance(n, int)})

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
        # A node with no conclusions states nothing yet. That is a legitimate starting point --
        # a stub records that a paper is in scope before anyone has transcribed a claim from it --
        # but every other report here iterates conclusions, so such a node is invisible in all of
        # them. Surfacing it is the whole difference between a stub and a forgotten directory.
        if not conclusions_of(node) and meta.get("status") != "deprecated":
            tasks.append(f"state     {node_id}  (no conclusions yet)")
        for conclusion in conclusions_of(node):
            kind = designated_kind(conclusion)
            issue = conclusion.get("issue")
            if issue is None:
                claim = "UNCLAIMED, no issue"
            elif issue in stale_issues:
                claim = f"#{issue} CLOSED -- reopen it, or drop the `issue` field"
            else:
                claim = f"#{issue}"
            if import_status(conclusion) == "undetermined":
                tasks.append(
                    f"imports   {node_id}.{conclusion.get('id')}  (not yet traced to its sources)")
            if kind == "none-yet":
                tasks.append(f"justify   {node_id}.{conclusion.get('id')}  [{claim}]")
            elif kind in {"literature", "asserted"}:
                tasks.append(f"formalize {node_id}.{conclusion.get('id')}  ({kind}) [{claim}]")

    print("Housekeeping queue")
    print("=" * 62)
    for task in tasks or ["  nothing outstanding"]:
        print(f"  {task}" if tasks else task)
    return True


# ---------------------------------------------------------------------------
# state: a committed snapshot of the network
# ---------------------------------------------------------------------------


def render_state(nodes: dict[str, dict]) -> str:
    """A committed snapshot of the network's shape, for people who do not run the tooling.

    Deliberately covers only what is derivable from the metadata, with no Lean, so that it stays
    cheap enough to regenerate in any pull request. Receipt freshness needs fingerprints and lives
    in `ieantn.py status` instead.

    Committing it buys two things. A maintainer can read the project's state from the repository
    rather than from a clone and a Python run — and, more usefully, **the diff of this file in a
    pull request says what the change did to the network**: a conclusion moving from `none-yet` to
    `lean-comparator` is one line.
    """
    index = index_conclusions(nodes)
    importers = importers_of(nodes)
    kinds: dict[str, int] = {}
    for _, conclusion in index.values():
        kind = designated_kind(conclusion) or "unset"
        kinds[kind] = kinds.get(kind, 0) + 1

    lines = [
        "# Network state",
        "",
        "**Generated file - do not edit.**  Regenerated by `python scripts/ieantn.py state`.",
        "",
        "Derived from node metadata alone. Receipt freshness needs Lean, and lives in",
        "`python scripts/ieantn.py status`.",
        "",
        f"{len(nodes)} node version(s), {len(index)} conclusion(s)."
        + (f"  {sum(1 for n in nodes.values() if not conclusions_of(n))} state nothing yet."
           if any(not conclusions_of(n) for n in nodes.values()) else ""),
        "",
        "## Evidence",
        "",
        "| Designated justification | Conclusions |",
        "|---|---:|",
    ]
    lines += [f"| `{kind}` | {count} |" for kind, count in sorted(kinds.items())]
    lines += [
        "",
        "## Nodes",
        "",
        "| Node | Status | Conclusion | Evidence | Imports | Issue |",
        "|---|---|---|---|---:|---|",
    ]
    for node_id, node in sorted(nodes.items()):
        status = (node.get("node") or {}).get("status", "?")
        if not conclusions_of(node):
            # One row per node rather than per conclusion, so a stub is not silently absent from
            # the snapshot that exists to say what the network contains.
            lines.append(f"| `{node_id}` | {status} | *(none yet)* | - | - | - |")
        for conclusion in conclusions_of(node):
            issue = conclusion.get("issue")
            lines.append(
                f"| `{node_id}` | {status} | `{conclusion.get('id')}` | "
                f"{designated_kind(conclusion)} | {len(conclusion.get('imports') or [])} | "
                + (f"#{issue} |" if issue else "- |")
            )

    ranked = sorted(((len(v), k) for k, v in importers.items()), reverse=True)
    if ranked:
        lines += [
            "",
            "## Leverage",
            "",
            "Conclusions the most others depend on. Refreshing these clears the most staleness",
            "downstream.",
            "",
            "| Conclusion | Dependants |",
            "|---|---:|",
        ]
        lines += [f"| `{key}` | {count} |" for count, key in ranked]
    return "\n".join(lines) + "\n"


def state(check_only: bool) -> bool:
    rendered = render_state(load_nodes())
    if check_only:
        problems = Problems()
        if (STATE.read_text(encoding="utf-8") if STATE.is_file() else "") != rendered:
            problems.add(rel(STATE), "out of date; run `python scripts/ieantn.py state`")
        return problems.report("network state")
    STATE.write_text(rendered, encoding="utf-8", newline="\n")
    print(f"wrote {rel(STATE)}")
    return True


# ---------------------------------------------------------------------------
# graph: the network as a page someone can read
# ---------------------------------------------------------------------------

#: How each kind of evidence is drawn. Lean-checked is the only one that is not a leaf of the
#: trust graph, so it is the only one drawn as settled.
EVIDENCE_STYLE = {
    "lean-comparator": ("verified", "#1a7f37", "#dafbe1"),
    "numerical": ("computation", "#9a6700", "#fff8c5"),
    "literature": ("cited", "#0969da", "#ddf4ff"),
    "asserted": ("asserted", "#bc4c00", "#fff1e5"),
    "bridged": ("bridged", "#8250df", "#fbefff"),
    "none-yet": ("unjustified", "#cf222e", "#ffebe9"),
}


#: Lines that end a declaration when they start one of their own.
_DECLARATION_START = ("def ", "noncomputable def ", "abbrev ", "theorem ", "lemma ", "/--",
                      "end ", "namespace ", "section ", "@[", "open ", "variable ")


def conclusions_source(node_id: str) -> pathlib.Path:
    return NODES_DIR / node_id.replace(".", "/") / "Conclusions.lean"


def read_declaration(node_id: str, cid: str) -> tuple[str, str]:
    """The docstring and the Lean source of one conclusion, as written.

    The docstring is where a node's informal statement lives -- there is no blueprint -- so a
    summary that omitted it would be a summary of the metadata rather than of the claim. And the
    source is the *Lean spelling*: the thing a reader has to match if they want to import it, and
    the thing that decides whether a transcription is faithful.
    """
    path = conclusions_source(node_id)
    if not path.is_file():
        return "", ""
    lines = path.read_text(encoding="utf-8").splitlines()
    start = None
    for number, line in enumerate(lines):
        stripped = line.lstrip()
        for prefix in ("def ", "noncomputable def ", "abbrev "):
            if stripped.startswith(prefix) and stripped[len(prefix):].split()[:1] == [cid]:
                start = number
                break
        if start is not None:
            break
    if start is None:
        return "", ""

    # The docstring is the /-- ... -/ block ending on the line before, if there is one.
    doc: list[str] = []
    if start and lines[start - 1].rstrip().endswith("-/"):
        end = start - 1
        begin = end
        while begin >= 0 and not lines[begin].lstrip().startswith("/--"):
            begin -= 1
        if begin >= 0:
            doc = lines[begin:end + 1]
            doc[0] = doc[0].lstrip()[3:].lstrip()
            doc[-1] = doc[-1].rstrip()[:-2].rstrip()
            doc = [line for line in doc if line is not None]

    body = [lines[start]]
    for line in lines[start + 1:]:
        stripped = line.lstrip()
        if stripped and not any(stripped.startswith(prefix) for prefix in _DECLARATION_START):
            body.append(line)
            continue
        break
    while body and not body[-1].strip():
        body.pop()
    return "\n".join(doc).strip(), "\n".join(body)


def declaration_url(key: str) -> str | None:
    """Where a reader can go to read the claim itself.

    A graph of claims whose boxes cannot be clicked makes the reader take the node id, guess the
    path, and search the file. This resolves the id to the exact line of the exact file.

    Source links rather than generated documentation, for now, deliberately: they need no hosting,
    no Pages, and no second build, and they cannot go stale relative to a commit. When doc-gen is
    published this is the one function to change -- the URL becomes
    `<pages>/docs/IEANTN/Nodes/<Family>/<version>/Conclusions.html#<declaration>` -- and every
    caller follows.
    """
    node_id, _, cid = key.rpartition(".")
    relative = pathlib.PurePosixPath("IEANTN/Nodes") / node_id.replace(".", "/") / "Conclusions.lean"  # noqa: E501
    path = ROOT / relative
    if not path.is_file():
        return None
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = line.lstrip()
        for prefix in ("def ", "noncomputable def ", "abbrev "):
            if stripped.startswith(prefix) and stripped[len(prefix):].split()[:1] == [cid]:
                return f"{REPOSITORY_URL}/blob/main/{relative}#L{number}"
    return None


#: The hexagon a bridge is drawn as, and the arrows into and out of it.
BRIDGE_STYLE = ("#8250df", "#fbefff")


def bridges_in(nodes: dict) -> list[dict]:
    """Every bridge in the network, as premises -> conclusion.

    A bridge is *not* an edge. `from` may name several conclusions, so a bridge is a many-to-one
    relation -- an implication with more than one hypothesis -- and an edge cannot carry that
    without lying about which premises were needed together. Drawing the bridge itself as a node,
    with an arrow in from each premise and one arrow out, is the ordinary way to draw a hyperedge
    and costs nothing when there is only one premise.
    """
    found = []
    for node_id, node in sorted(nodes.items()):
        for conclusion in conclusions_of(node):
            target = f"{node_id}.{conclusion.get('id')}"
            designated = conclusion.get("designated")
            for justification in conclusion.get("justifications") or []:
                if justification.get("kind") != "bridged":
                    continue
                found.append({
                    "id": f"{target}::{justification.get('id')}",
                    "file": str(justification.get("bridge") or ""),
                    "premises": bridge_sources(justification),
                    "conclusion": target,
                    "designated": justification.get("id") == designated,
                })
    return found


#: Evidence kinds from weakest to strongest. A node is summarised by its *weakest* conclusion,
#: because that is what a reader of the whole node is actually relying on: a node with nine
#: verified claims and one bare assertion is, for anyone importing all ten, an assertion.
EVIDENCE_ORDER = ["none-yet", "asserted", "literature", "numerical", "bridged", "lean-comparator"]


def weakest_kind(conclusions: list[dict]) -> str:
    """The least-supported evidence kind among these conclusions."""
    kinds = [designated_kind(c) or "none-yet" for c in conclusions]
    return min(kinds, key=lambda k: EVIDENCE_ORDER.index(k) if k in EVIDENCE_ORDER else 0)


def click_lines(index: dict, prefix: str = "", key=None) -> list[str]:
    """`click` directives making the boxes navigable.

    Mermaid renders these as links on GitHub. Emitted once per distinct target so the collapsed
    view, whose boxes stand for whole nodes, links to the first claim in the node rather than
    repeating a link per claim.
    """
    out, seen = [], set()
    for conclusion_key in sorted(index):
        box = (key(conclusion_key) if key else conclusion_key)
        if box in seen:
            continue
        node_id, _, cid = conclusion_key.rpartition(".")
        url = node_page_url(node_id, "" if key else cid, from_root=True)
        seen.add(box)
        out.append(f'  click {prefix}{mermaid_id(box)} href "{url}" _blank')
    return out


def render_node_overview(nodes: dict[str, dict], index: dict) -> list[str]:
    """One box per node, edges aggregated with a count.

    The per-conclusion picture is the truth, but it grows with the network and stops being
    readable well before the network stops being interesting. This one grows only with the number
    of papers, which is the scale a reader can actually hold.
    """
    lines = ["```mermaid", "graph LR"]
    for node_id in sorted(nodes):
        cs = conclusions_of(nodes[node_id])
        if cs:
            kind = weakest_kind(cs)
            label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
            count = f"{len(cs)} claim" + ("s" if len(cs) != 1 else "")
            caption = f"{count}<br/><i>weakest: {label}</i>"
        else:
            caption = "<i>nothing stated yet</i>"
        lines.append(f'  N{mermaid_id(node_id)}["<b>{node_id}</b><br/>{caption}"]')

    tally: dict = {}
    for key in sorted(index):
        target_node = key.rsplit(".", 1)[0]
        for dependency in index[key][1].get("imports") or []:
            source = f"{dependency.get('node')}.{dependency.get('conclusion')}"
            if source in index:
                pair = (source.rsplit(".", 1)[0], target_node)
                if pair[0] != pair[1]:
                    tally[pair] = tally.get(pair, 0) + 1
    for (source_node, target_node), count in sorted(tally.items()):
        arrow = f"-->|{count}|" if count > 1 else "-->"
        lines.append(f"  N{mermaid_id(source_node)} {arrow} N{mermaid_id(target_node)}")

    # Bridges are collapsed to node-to-node arrows here. The premises of one bridge may sit in
    # different nodes, so this loses the "needed together" that the hexagon carries -- which is
    # why the detailed picture keeps the hexagon and this one says only that a bridge exists.
    crossings = {(premise.rsplit(".", 1)[0], bridge["conclusion"].rsplit(".", 1)[0])
                 for bridge in bridges_in(nodes) for premise in bridge["premises"]}
    for source_node, target_node in sorted(crossings):
        if source_node != target_node and source_node in nodes and target_node in nodes:
            lines.append(f"  N{mermaid_id(source_node)} ==>|bridge| N{mermaid_id(target_node)}")

    for node_id in sorted(nodes):
        cs = conclusions_of(nodes[node_id])
        if cs and any(import_status(c) == "undetermined" for c in cs):
            lines.append(f"  style N{mermaid_id(node_id)} stroke-dasharray: 6 4;")
    for kind in EVIDENCE_ORDER:
        members = [f"N{mermaid_id(n)}" for n in sorted(nodes)
                   if (weakest_kind(conclusions_of(nodes[n]))
                       if conclusions_of(nodes[n]) else "none-yet") == kind]
        if members:
            lines.append(f"  class {','.join(members)} {mermaid_id(kind)};")
    lines += click_lines(index, prefix="N", key=lambda k: k.rsplit(".", 1)[0])
    lines += ["```", ""]
    return lines


def mermaid_id(key: str) -> str:
    """A Mermaid node id: letters, digits and underscores only.

    Dots, dashes and colons all appear in the keys this is called on -- `Lcm.v1.main`, the
    `bridged` justification ids, the evidence kind `lean-comparator` -- and every one of them
    ends a node id early in Mermaid, which fails at render time rather than here.
    """
    return re.sub(r"[^0-9A-Za-z_]", "_", key)


def render_graph(nodes: dict[str, dict]) -> str:
    """`GRAPH.md`: what the network contains and what it rests on.

    Written for someone who has not cloned the repository and is not running an agent: the
    dependency structure is the thing worth showing, and until now it could only be seen by running
    `report`. The Mermaid block renders on GitHub without anything being hosted, so the picture and
    the prose stay in the same generated file and cannot drift apart.
    """
    index = index_conclusions(nodes)
    importers = importers_of(nodes)

    lines = [
        "# The network",
        "",
        "**Generated file - do not edit.**  Regenerated by `python scripts/ieantn.py graph`.",
        "",
        "Each **node** makes a mathematical claim, declares what it assumes, and carries evidence",
        "for the step from its assumptions to its claim. An arrow `A --> B` means *B assumes A*:",
        "B's claim is conditional on A's, and B's own evidence covers only the step.",
        "",
        "The colour of a box is the kind of evidence, and only green is checked by Lean here.",
        "Everything else is a leaf of the trust graph -- something the network takes on faith,",
        "however reasonably -- and the point of drawing it is that you can see exactly which.",
        "",
        "A **dashed** border means nobody has yet worked out what that claim itself assumes. It is",
        "not a claim that the box rests on nothing; it is an admission that the question has not",
        "been asked. A solid border means someone has traced it to its sources, and the arrows",
        "into it are the answer.",
        "",
        "Every box and every claim named below links to that node's page, which carries the Lean",
        "spelling of the claim, its docstring, and everything recorded about why it should be",
        "believed. The pages are indexed at [docs/nodes/](docs/nodes/README.md).",
        "",
        "A **hexagon** is a *bridge*, and the thick arrows around it are a different relation from",
        "the thin ones. A thin arrow into a box means the box **assumes** what the arrow comes",
        "from, and nothing here checks the step. A bridge is the step itself, proved in Lean and",
        "recompiled on every push. It is drawn as a box rather than an arrow because a bridge may",
        "have several premises at once, which an arrow cannot say. A bridge marked *spare* is a",
        "second ground for a claim that is currently justified some other way.",
        "",
    ]

    # --- the two pictures ----------------------------------------------------------------
    class_defs = [
        f"  classDef {mermaid_id(kind)} fill:{fill},stroke:{stroke},color:#1f2328;"
        for kind, (_, stroke, fill) in EVIDENCE_STYLE.items()]
    bridge_class_def = (f"  classDef bridge fill:{BRIDGE_STYLE[1]},stroke:{BRIDGE_STYLE[0]},"
                        "color:#1f2328,stroke-width:2px;")

    lines += [
        "## The network at a glance",
        "",
        "One box per node, so this stays readable as the network grows. The number on a thin arrow",
        "is how many separate claims cross it. A node is coloured by its **weakest** conclusion,",
        "since that is what someone importing the whole node is relying on, and dashed if any of",
        "its claims has not been traced to its own sources.",
        "",
        "A thick **bridge** arrow is a Lean-checked implication rather than an assumption. At this",
        "resolution it says only that some bridge crosses between the two nodes; which premises a",
        "bridge needed together is in the detailed picture below.",
        "",
    ]
    overview = render_node_overview(nodes, index)
    lines += overview[:-2] + class_defs + overview[-2:]

    lines += [
        "## Every claim",
        "",
        "The same graph at full resolution, grouped by node. This is the one that is true rather",
        "than the one that is legible; when they disagree, believe this one.",
        "",
    ]
    lines += ["```mermaid", "graph LR"]
    for node_id in sorted(nodes):
        keys = [k for k in sorted(index) if k.rsplit(".", 1)[0] == node_id]
        if not keys:
            continue
        lines.append(f'  subgraph sg{mermaid_id(node_id)}["{node_id}"]')
        for key in keys:
            _, conclusion = index[key]
            kind = designated_kind(conclusion) or "none-yet"
            label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "#57606a", "#f6f8fa"))
            cid = key.rsplit(".", 1)[1]
            lines.append(f'    {mermaid_id(key)}["<b>{cid}</b><br/><i>{label}</i>"]')
        lines.append("  end")
    for key in sorted(index):
        _, conclusion = index[key]
        for dependency in conclusion.get("imports") or []:
            source = f"{dependency.get('node')}.{dependency.get('conclusion')}"
            if source in index:
                lines.append(f"  {mermaid_id(source)} --> {mermaid_id(key)}")
    bridges = bridges_in(nodes)
    for bridge in bridges:
        if bridge["conclusion"] not in index:
            continue
        stem = pathlib.PurePosixPath(bridge["file"]).stem or "bridge"
        role = "" if bridge["designated"] else "<br/><i>spare</i>"
        bid = "BR" + mermaid_id(bridge["id"])
        lines.append(f'  {bid}{{{{"<b>{stem}</b>{role}"}}}}')
        for premise in bridge["premises"]:
            if premise in index:
                lines.append(f"  {mermaid_id(premise)} ==> {bid}")
        lines.append(f"  {bid} ==> {mermaid_id(bridge['conclusion'])}")

    for key in sorted(index):
        if import_status(index[key][1]) == "undetermined":
            lines.append(f"  style {mermaid_id(key)} stroke-dasharray: 6 4;")
    seen_kinds = {designated_kind(c) or "none-yet" for _, c in index.values()}
    lines += class_defs + [bridge_class_def]
    bridge_ids = ["BR" + mermaid_id(b["id"]) for b in bridges if b["conclusion"] in index]
    if bridge_ids:
        lines.append(f"  class {','.join(bridge_ids)} bridge;")
    for kind in sorted(seen_kinds):
        members = [mermaid_id(k) for k in sorted(index)
                   if (designated_kind(index[k][1]) or "none-yet") == kind]
        if members:
            lines.append(f"  class {','.join(members)} {mermaid_id(kind)};")
    lines += click_lines(index)
    lines += ["```", ""]

    # --- what it rests on --------------------------------------------------------------
    roots = sorted(key for key in index if not importers.get(key))
    lines += [
        "## What each result rests on",
        "",
        "Only the conclusions nothing else imports are listed; the rest appear inside them.",
        "A line is one claim, indented under whatever assumes it.",
        "",
    ]

    def walk(key: str, depth: int, seen: set[str], out: list[str]) -> None:
        _, conclusion = index[key]
        kind = designated_kind(conclusion) or "none-yet"
        label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
        mark = "  " * depth
        repeated = " *(above)*" if key in seen else ""
        pending = (" — *sources not traced*"
                   if import_status(conclusion) == "undetermined" else "")
        node_id, _, cid = key.rpartition(".")
        shown = f"[`{key}`]({node_page_url(node_id, cid, from_root=True)})"
        out.append(f"{mark}- {shown} — {label}{repeated}{pending}")
        if key in seen:
            return
        seen.add(key)
        for dependency in conclusion.get("imports") or []:
            source = f"{dependency.get('node')}.{dependency.get('conclusion')}"
            if source in index:
                walk(source, depth + 1, seen, out)

    for root in roots:
        block: list[str] = []
        walk(root, 0, set(), block)
        lines += block + [""]

    # --- the leaves --------------------------------------------------------------------
    leaves = sorted(
        (key for key in index
         if (designated_kind(index[key][1]) or "none-yet") not in VERIFIED_KINDS),
        key=lambda k: (-len(importers.get(k, [])), k))
    if leaves:
        lines += [
            "## What the network takes on trust",
            "",
            "Every claim above that Lean has not checked here, ordered by how much depends on it.",
            "This table is the honest answer to \"how good is the evidence\", and it is computed",
            "rather than maintained.",
            "",
            "| Claim | Evidence | Depended on by | Its own sources |",
            "|---|---|---:|---|",
        ]
        for key in leaves:
            kind = designated_kind(index[key][1]) or "none-yet"
            label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
            traced = ("**not yet traced**"
                      if import_status(index[key][1]) == "undetermined" else "traced")
            node_id, _, cid = key.rpartition(".")
            shown = f"[`{key}`]({node_page_url(node_id, cid, from_root=True)})"
            lines.append(
                f"| {shown} | {label} | {len(importers.get(key, []))} | {traced} |")
        lines.append("")

    # --- nodes with nothing stated yet --------------------------------------------------
    empty = sorted(node_id for node_id, node in nodes.items() if not conclusions_of(node))
    if empty:
        lines += [
            "## Nodes that state nothing yet",
            "",
            "A paper recorded as in scope, before anyone has transcribed a claim from it. These are",
            "the network's open invitations.",
            "",
        ]
        lines += [f"- [`{node_id}`]({node_page_url(node_id, from_root=True)})"
                  for node_id in empty]
        lines.append("")

    lines += [
        "---",
        "",
        "See [STATE.md](STATE.md) for the same content as a table, [docs/ARCHITECTURE.md]"
        "(docs/ARCHITECTURE.md)",
        "for why the network is shaped this way, and `python scripts/ieantn.py status` for how",
        "fresh each Lean verification is.",
    ]
    return "\n".join(lines) + "\n"


def node_page_path(node_id: str) -> pathlib.Path:
    return PAGES / f"{node_id.replace('.', '-')}.md"


def node_page_url(node_id: str, anchor: str = "", from_root: bool = False) -> str:
    """A link to a node's page.

    `from_root` because GRAPH.md sits at the repository root and the node pages link to each other
    from inside `docs/nodes/`; a path that is right for one is broken for the other.
    """
    fragment = f"#{anchor}" if anchor else ""
    prefix = "docs/nodes/" if from_root else ""
    return f"{prefix}{node_id.replace('.', '-')}.md{fragment}"


def _quote(value) -> str:
    """One metadata value, flattened onto a line and safe inside a table cell."""
    if isinstance(value, list):
        return ", ".join(_quote(entry) for entry in value)
    return " ".join(str(value or "").split()).replace("|", "\\|")


def render_node_page(node_id: str, nodes: dict, index: dict, importers: dict) -> str:
    """Everything recorded about one node, for someone who is not going to read the YAML.

    The metadata is the justification: a node's claim is only as good as what stands behind it,
    and that lives in `formalization.yaml` in a shape built for machines. This is the same content
    for a person -- with the Lean spelling next to each claim, since that is what a consumer has
    to write and what decides whether a transcription is faithful.
    """
    node = nodes[node_id]
    meta, project = node.get("node") or {}, node.get("project") or {}
    out = [
        f"# `{node_id}`",
        "",
        "**Generated file - do not edit.**  Regenerated by `python scripts/ieantn.py pages`.",
        "",
        f"> {_quote(project.get('description')) or '_No description recorded._'}",
        "",
        "| | |",
        "|---|---|",
        f"| Kind | {_quote(meta.get('kind'))} |",
        f"| Status | {_quote(meta.get('status'))} |",
        f"| Maintainers | {_quote(project.get('responsible_maintainers'))} |",
        f"| Licence | {_quote(project.get('license'))} |",
        f"| Review | {_quote((node.get('review') or {}).get('status'))} |",
        "",
    ]

    sources = node.get("sources") or []
    if sources:
        out += ["## The source", ""]
        for source in sources:
            title = _quote(source.get("title"))
            authors = _quote(source.get("authors"))
            where = _quote(source.get("location") or source.get("id"))
            out.append(f"- **{title}** — {authors}. {where}"
                       + (f"  \n  _{_quote(source.get('note'))}_" if source.get("note") else ""))
        out.append("")

    conclusions = conclusions_of(node)
    out += ["## Conclusions", ""]
    if not conclusions:
        out += ["_This node states nothing yet._  It records that the source is in scope and "
                "carries its citation, so a conclusion can be added the moment something needs "
                "one.", ""]
    for conclusion in conclusions:
        cid = str(conclusion.get("id") or "")
        key = f"{node_id}.{cid}"
        doc, body = read_declaration(node_id, cid)
        url = declaration_url(key)
        out += [f"### `{cid}`", ""]
        if doc:
            out += [doc, ""]
        if body:
            out += ["```lean", body, "```", ""]
        out += [f"| | |", "|---|---|",
                f"| Lean name | `{_quote(conclusion.get('declaration'))}` |",
                f"| Challenge | `{_quote(conclusion.get('challenge'))}` |"]
        if url:
            out.append(f"| Source | [{conclusions_source(node_id).name}]({url}) |")
        kind = designated_kind(conclusion) or "none-yet"
        label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
        out.append(f"| Evidence | {label} (`{kind}`) |")
        out.append(f"| Sources traced | {import_status(conclusion)} |")
        depends = [f"{d.get('node')}.{d.get('conclusion')}" for d in conclusion.get("imports") or []]
        out.append("| Assumes | " + (", ".join(
            f"[`{d}`]({node_page_url(d.rsplit('.', 1)[0], d.rsplit('.', 1)[1])})"
            for d in depends) or "nothing recorded") + " |")
        used_by = importers.get(key) or []
        out.append("| Assumed by | " + (", ".join(
            f"[`{u}`]({node_page_url(u.rsplit('.', 1)[0], u.rsplit('.', 1)[1])})"
            for u in sorted(used_by)) or "nothing yet") + " |")
        out.append("")

        for justification in conclusion.get("justifications") or []:
            jid = justification.get("id")
            mark = " — **designated**" if jid == conclusion.get("designated") else ""
            out.append(f"**Justification `{jid}`**{mark} — {_quote(justification.get('kind'))}"
                       + (f", {_quote(justification.get('locator'))}"
                          if justification.get("locator") else ""))
            if justification.get("from"):
                out.append(f"  \n  Bridged from {_quote(bridge_sources(justification))}"
                           f" via `{_quote(justification.get('bridge'))}`.")
            if justification.get("note"):
                out += ["", f"> {_quote(justification.get('note'))}"]
            out.append("")

    limitations = node.get("limitations") or []
    if limitations:
        out += ["## Limitations", "",
                "Recorded by the node itself, not derived.", ""]
        out += [f"- {_quote(limitation)}" for limitation in limitations] + [""]

    automation = (node.get("automation") or {}).get("methods") or []
    if automation:
        out += ["## How this node was made", ""]
        for method in automation:
            out.append(f"- **{_quote(method.get('method'))}**"
                       + (f" ({_quote(method.get('models'))})" if method.get("models") else "")
                       + (f" — {_quote(method.get('role'))}" if method.get("role") else ""))
        out.append("")

    out += ["---", "",
            f"[All nodes](README.md) · [The network](../../GRAPH.md) · "
            f"[State](../../STATE.md)"]
    return "\n".join(out) + "\n"


def render_pages_index(nodes: dict, index: dict) -> str:
    out = [
        "# Nodes",
        "",
        "**Generated file - do not edit.**  Regenerated by `python scripts/ieantn.py pages`.",
        "",
        "One page per node: what it claims, in Lean and in prose, and everything recorded about "
        "why it should be believed. [GRAPH.md](../../GRAPH.md) is the same network as a picture.",
        "",
        "| Node | Kind | Claims | Weakest evidence |",
        "|---|---|---:|---|",
    ]
    for node_id in sorted(nodes):
        node = nodes[node_id]
        cs = conclusions_of(node)
        kind = weakest_kind(cs) if cs else "none-yet"
        label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
        out.append(f"| [`{node_id}`]({node_id.replace('.', '-')}.md) "
                   f"| {_quote((node.get('node') or {}).get('kind'))} | {len(cs)} "
                   f"| {label if cs else '—'} |")
    out.append("")
    return "\n".join(out) + "\n"


def pages(check_only: bool) -> bool:
    """Write (or verify) one page per node."""
    nodes = load_nodes()
    index = index_conclusions(nodes)
    importers = importers_of(nodes)
    wanted = {node_page_path(node_id): render_node_page(node_id, nodes, index, importers)
              for node_id in sorted(nodes)}
    wanted[PAGES / "README.md"] = render_pages_index(nodes, index)

    if check_only:
        problems = Problems()
        for path, text in sorted(wanted.items()):
            current = path.read_text(encoding="utf-8") if path.is_file() else ""
            if current != text:
                problems.add(rel(path), "out of date; run `python scripts/ieantn.py pages`")
        for path in sorted(PAGES.glob("*.md")) if PAGES.is_dir() else []:
            if path not in wanted:
                problems.add(rel(path), "no such node; delete it and rerun `pages`")
        return problems.report("node pages")

    PAGES.mkdir(parents=True, exist_ok=True)
    for path in sorted(PAGES.glob("*.md")):
        if path not in wanted:
            path.unlink()
            print(f"removed {rel(path)}")
    for path, text in sorted(wanted.items()):
        path.write_text(text, encoding="utf-8", newline="\n")
    print(f"wrote {len(wanted)} pages under {rel(PAGES)}")
    return True


def graph(check_only: bool) -> bool:
    rendered = render_graph(load_nodes())
    if check_only:
        problems = Problems()
        if (GRAPH.read_text(encoding="utf-8") if GRAPH.is_file() else "") != rendered:
            problems.add(rel(GRAPH), "out of date; run `python scripts/ieantn.py graph`")
        return problems.report("network graph")
    GRAPH.write_text(rendered, encoding="utf-8", newline="\n")
    print(f"wrote {rel(GRAPH)}")
    return True


# ---------------------------------------------------------------------------
# diff: what this branch degrades
# ---------------------------------------------------------------------------


def git_show(ref: str, path: str) -> str | None:
    """The contents of `path` at `ref`, or None if it did not exist there."""
    finished = subprocess.run(
        ["git", "show", f"{ref}:{path}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return finished.stdout if finished.returncode == 0 else None


def state_at(ref: str | None) -> dict:
    """The graph as it stands at `ref`, or in the working tree when `ref` is None.

    Reading the base state needs no Lean at all: `fingerprints.json` is committed, so the
    statements as they were are recoverable with `git show`. That is most of why this check is
    cheap enough to run on every pull request.
    """
    if ref is None:
        nodes = load_nodes()
        fingerprints = (
            json.loads(FINGERPRINTS.read_text(encoding="utf-8")) if FINGERPRINTS.is_file() else {}
        )
        receipts = {
            path.stem: json.loads(path.read_text(encoding="utf-8"))
            for path in (RECEIPTS.glob("*.json") if RECEIPTS.is_dir() else [])
        }
    else:
        listing = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ref],
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
        ).stdout.splitlines()
        nodes = {}
        for path in listing:
            if path.startswith("IEANTN/Nodes/") and path.endswith("formalization.yaml"):
                raw = git_show(ref, path)
                if raw is None:
                    continue
                data = yaml.safe_load(raw) or {}
                directory = ROOT / pathlib.PurePosixPath(path).parent
                data["_dir"] = directory
                nodes[node_id_of(directory)] = data
        raw = git_show(ref, "fingerprints.json")
        fingerprints = json.loads(raw) if raw else {}
        receipts = {}
        for path in listing:
            if path.startswith("receipts/") and path.endswith(".json"):
                raw = git_show(ref, path)
                if raw:
                    receipts[pathlib.PurePosixPath(path).stem] = json.loads(raw)

    conclusions = {}
    for node_id, node in nodes.items():
        for conclusion in conclusions_of(node):
            conclusions[f"{node_id}.{conclusion.get('id')}"] = {
                "imports": [
                    f"{d.get('node')}.{d.get('conclusion')}"
                    for d in (conclusion.get("imports") or [])
                ],
                "kind": designated_kind(conclusion),
            }
    return {"conclusions": conclusions, "fingerprints": fingerprints, "receipts": receipts}


def acknowledged() -> dict[str, str]:
    """Conclusions this branch explicitly acknowledges breaking, and why.

    An override, not a routine step -- see CONTRIBUTING.md. It exists for the case where a change
    is genuinely breaking and has to land anyway, and its value comes from being rare enough that a
    reviewer notices one in the diff.
    """
    result: dict[str, str] = {}
    for path in sorted(CHANGES.glob("*.yaml")) if CHANGES.is_dir() else []:
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
        for entry in data.get("acknowledge") or []:
            if entry.get("conclusion"):
                result[entry["conclusion"]] = entry.get("reason", "(no reason given)")
    return result


def diff(base: str) -> bool:
    """Report what this branch degrades, and fail on the one class that must not be silent."""
    before, after = state_at(base), state_at(None)
    excused = acknowledged()
    errors: list[str] = []
    warnings: list[str] = []
    notes: list[str] = []

    importers_before: dict[str, list[str]] = {}
    for key, entry in before["conclusions"].items():
        for target in entry["imports"]:
            importers_before.setdefault(target, []).append(key)

    for key, entry in sorted(before["conclusions"].items()):
        old = before["fingerprints"].get(key)
        new = after["fingerprints"].get(key)

        if key not in after["conclusions"]:
            users = importers_before.get(key, [])
            if users:
                errors.append(
                    f"**`{key}` was removed** but {len(users)} conclusion(s) still import it at "
                    f"the base: {', '.join(f'`{u}`' for u in users)}."
                )
            else:
                notes.append(f"`{key}` removed; nothing imported it.")
            continue

        if old is None or new is None or old == new:
            continue

        users = importers_before.get(key, [])
        had_receipt = key in before["receipts"]
        detail = []
        if users:
            detail.append(f"{len(users)} importer(s): " + ", ".join(f"`{u}`" for u in users))
        if had_receipt:
            detail.append("a recorded receipt")

        if not detail:
            notes.append(f"`{key}` restated; nothing depended on it.")
        elif key in excused:
            warnings.append(
                f"**`{key}` edited in place** ({'; '.join(detail)}) -- acknowledged: "
                f"{excused[key]}"
            )
        else:
            errors.append(
                f"**`{key}` was edited in place**, and it has {'; '.join(detail)}.\n\n"
                f"  Editing a conclusion others depend on changes what *they* claim. Make a new "
                f"version instead:\n\n  ```bash\n  python scripts/ieantn.py new-version "
                f"{key.split('.')[0]}\n  ```\n\n  If this must land anyway, add a `changes/*.yaml` "
                f"acknowledgement (see CONTRIBUTING.md)."
            )

    for key, receipt in sorted(after["receipts"].items()):
        for name, digest in (receipt.get("statement") or {}).items():
            if after["fingerprints"].get(name) != digest:
                warnings.append(
                    f"Receipt for `{key}` is now **BROKEN**: `{name}` no longer matches what was "
                    "verified."
                )
                break

    for key, entry in sorted(after["conclusions"].items()):
        if key not in before["conclusions"]:
            notes.append(f"new conclusion `{key}` (`{entry['kind']}`).")

    # Vocabulary is this repository's core: shared by every node, and so the one place a single
    # edit can change what many conclusions claim. Mathlib gives its core files the same extra
    # scrutiny, for the same reason. The fingerprints already carry the blast radius, so report it
    # rather than leaving a reviewer to work out what a Vocabulary diff touched.
    touched = subprocess.run(
        ["git", "diff", "--name-only", base],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    ).stdout.splitlines()
    if any(line.startswith("IEANTN/Vocabulary/") for line in touched):
        moved = [
            key
            for key in sorted(before["conclusions"])
            if key in after["conclusions"]
            and before["fingerprints"].get(key) != after["fingerprints"].get(key)
        ]
        if moved:
            shown = ", ".join(f"`{key}`" for key in moved[:10])
            warnings.append(
                f"**Vocabulary changed**, moving {len(moved)} conclusion fingerprint(s): {shown}"
                + (" and others" if len(moved) > 10 else "")
                + ". Vocabulary is shared by every node, so this warrants the scrutiny a change to "
                "a Mathlib core file would get. In particular, check that nothing added here "
                "duplicates a definition that already exists."
            )
        else:
            notes.append(
                "Vocabulary changed, but no conclusion fingerprint moved, so the change is "
                "additive or cosmetic."
            )

    lines = ["## Network impact", ""]
    if not (errors or warnings or notes):
        lines.append("No change to any statement, dependency, or receipt.")
    for heading, items in (
        ("### Breaking", errors),
        ("### Degraded", warnings),
        ("### Informational", notes),
    ):
        if items:
            lines += [heading, ""] + [f"- {item}" for item in items] + [""]
    report = "\n".join(lines)
    print(report)

    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write(report + "\n")

    return not errors


# ---------------------------------------------------------------------------
# spinoff: emit one conclusion as a standalone Palomar submission
# ---------------------------------------------------------------------------

#: The namespace the emitted Challenge declares its compared theorem in. Anything but the node's
#: own, which the library already uses for the generated challenge.
SPINOFF_NAMESPACE = "Spinoff"


def unjustified_leaves(index: dict, key: str, seen: set[str] | None = None) -> list[str]:
    """The conclusion keys `key` transitively rests on that Lean has not checked here.

    The same walk `report` prints, returning keys rather than prose. These become the emitted
    Challenge's hypotheses: a Palomar submission cannot assert what this network is content to
    take on a citation's authority, so it must say what it is assuming.
    """
    seen = set() if seen is None else seen
    if key in seen or key not in index:
        return []
    seen.add(key)
    _, conclusion = index[key]
    justification = designated_of(conclusion) or {}
    found: list[str] = []
    if justification.get("kind") == "bridged":
        for source in bridge_sources(justification):
            found += unjustified_leaves(index, source, seen)
    elif justification.get("kind") not in VERIFIED_KINDS:
        found.append(key)
    for dependency in conclusion.get("imports") or []:
        found += unjustified_leaves(
            index, f"{dependency.get('node')}.{dependency.get('conclusion')}", seen)
    return found


def opens_of(path: pathlib.Path) -> list[str]:
    """The module-level `open` directives of a Lean file.

    `open ... in` is excluded: it scopes to the single declaration that follows, so it is
    already inside whatever text gets sliced.
    """
    code = strip_lean_comments(path.read_text(encoding="utf-8"))
    return [line.rstrip() for line in code.splitlines()
            if re.match(r"^open\s", line) and not line.rstrip().endswith(" in")]


def module_path(module: str) -> pathlib.Path:
    return ROOT / pathlib.PurePosixPath(module.replace(".", "/") + ".lean")


def slice_source(text: str, decl: dict, prefix: str) -> tuple[str, str]:
    """The source of one declaration, and the namespace it must be re-emitted inside.

    Lean reports 1-based lines and 0-based columns. The `range` spans the whole declaration
    including its docstring; the `selectionRange` spans just the declared name as written, and the
    namespace is the full name with that suffix removed -- see Tools/Spinoff.lean.
    """
    lines = text.splitlines()

    def cut(sl: int, sc: int, el: int, ec: int) -> str:
        if sl == el:
            return lines[sl - 1][sc:ec]
        out = [lines[sl - 1][sc:]] + lines[sl:el - 1] + [lines[el - 1][:ec]]
        return "\n".join(out)

    body = cut(decl["startLine"], decl["startCol"], decl["endLine"], decl["endCol"])
    written = cut(decl["nameStartLine"], decl["nameStartCol"],
                  decl["nameEndLine"], decl["nameEndCol"])
    full = decl["name"]
    if not full.endswith(written):
        raise SystemExit(
            f"error: {full} is written as `{written}`, which is not a suffix of its full name. "
            "The namespace cannot be recovered; refusing to guess.")
    namespace = full[: len(full) - len(written)].rstrip(".")
    del prefix
    return body, namespace


def spinoff(key: str, out: str, compile_check: bool) -> bool:
    """Emit one conclusion as a self-contained Palomar submission.

    See docs/ARCHITECTURE.md section 7. The Challenge inlines every IEANTN definition the statement
    needs, so its import closure is Mathlib-only as Palomar requires; the Solution reaches the real
    proof by depending on this repository.
    """
    nodes = load_nodes()
    index = index_conclusions(nodes)
    if key not in index:
        print(f"error: unknown conclusion `{key}`; try `python scripts/ieantn.py report`")
        return False
    node_id, conclusion = index[key]
    cid = conclusion.get("id")

    designated = designated_of(conclusion) or {}
    if designated.get("kind") not in VERIFIED_KINDS:
        print(f"error: `{key}` designates `{designated.get('kind')}`, so there is no Lean proof to "
              "submit. Palomar records a verified formalization, not a claim.")
        return False

    # Multi-level composition -- chaining several nodes' solutions into one -- is the part of
    # ARCHITECTURE section 7 that is not built. Refuse rather than emit something that looks
    # complete and is not.
    leaves = sorted(set(unjustified_leaves(index, key)))
    direct = {f"{d.get('node')}.{d.get('conclusion')}" for d in (conclusion.get("imports") or [])}
    deeper = [leaf for leaf in leaves if leaf not in direct]
    if deeper:
        print(f"error: `{key}` rests on {', '.join(deeper)}, which are not among its direct "
              "imports. Emitting that needs the per-node solutions composed along the way, which "
              "is not implemented; only a one-level spin-off is supported today.")
        return False

    solution_dir = SOLUTIONS / node_id
    if not (solution_dir / "Solution.lean").is_file():
        print(f"error: no solution at {rel(solution_dir)}")
        return False

    wanted = [conclusion.get("declaration")] + [index[leaf][1].get("declaration") for leaf in leaves]
    finished = subprocess.run(
        ["lake", "exe", "ieantn_spinoff", *[w for w in wanted if w]],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if finished.returncode != 0:
        sys.exit("error: could not locate the definitions to inline. Is `ieantn_spinoff` built?\n"
                 "       try `lake build ieantn_spinoff`\n" + (finished.stderr or "").strip())
    payload = next(
        (line for line in reversed(finished.stdout.splitlines()) if line.startswith("{")), None)
    if payload is None:
        sys.exit("error: ieantn_spinoff produced no output")
    declarations = json.loads(payload)["declarations"]

    target = ROOT / out
    target.mkdir(parents=True, exist_ok=True)

    # --- Challenge: the inlined definitions, then the compared theorem -----------------------
    sources = {d["module"]: module_path(d["module"]).read_text(encoding="utf-8")
               for d in declarations}
    mathlib_imports = sorted({
        module for path in {module_path(m) for m in sources}
        for module in imports_of(path) if under(module, "Mathlib")})

    blocks: list[str] = []
    current: tuple[str, str] | None = None
    for decl in declarations:
        body, namespace = slice_source(sources[decl["module"]], decl, decl["name"])
        here = (decl["module"], namespace)
        if here != current:
            if current is not None:
                blocks.append(f"end {current[1]}\n\n")
            blocks.append(f"namespace {namespace}\n" if namespace else "")
            # A definition body uses whatever its own file had `open`. `log x` and
            # `sigma 1 m` below mean `Real.log` and `ArithmeticFunction.sigma` only because
            # their source files open those namespaces; without this the inlined text does
            # not resolve. Scoped inside the namespace rather than unioned at the top, so two
            # modules cannot make each other's names ambiguous.
            for directive in opens_of(module_path(decl["module"])):
                blocks.append(directive + "\n")
            current = here
        blocks.append("\n" + body + "\n")
    if current:
        blocks.append(f"end {current[1]}\n")

    binders = "".join(
        f"\n    ({hypothesis_name({'node': leaf.rsplit('.', 1)[0], 'conclusion': leaf.rsplit('.', 1)[1]})} : "
        f"{index[leaf][1].get('declaration')})"
        for leaf in leaves)
    statement = conclusion.get("declaration")
    theorem = (f"theorem {SPINOFF_NAMESPACE}.main{binders} :\n    {statement} := by\n  sorry\n"
               if binders else
               f"theorem {SPINOFF_NAMESPACE}.main : {statement} := by\n  sorry\n")

    rests_on = ("\n".join(f"* `{leaf}`, taken as a hypothesis." for leaf in leaves)
                or "* nothing. Every definition it needs is inlined below and the statement is "
                   "unconditional.")
    challenge = (
        LICENCE_HEADER
        + "".join(f"import {module}\n" for module in mathlib_imports)
        + f"""
/-!
# Challenge: `{key}`

Spun off from the IEANTN network ({REPOSITORY_URL}), node `{node_id}`.
**Generated file** -- regenerated by `python scripts/ieantn.py spinoff {key}`.

The definitions below are inlined from that repository's `IEANTN/Vocabulary/` and the node's
`Conclusions.lean`, verbatim and with their docstrings, so that this file's import closure is Lean
core and Mathlib only. They keep their original names: the Solution obtains the identical constants
by depending on the repository, and Comparator compares the two exported environments, so a
divergence between an inlined copy and the real definition is exactly what it would catch.

What the statement rests on:

{rests_on}
-/

"""
        + "".join(blocks)
        + "\n"
        + theorem)
    (target / "Challenge.lean").write_text(challenge, encoding="utf-8", newline="\n")

    # --- Solution --------------------------------------------------------------------------
    vendored = sorted(path.stem for path in solution_dir.glob("*.lean"))
    arguments = " ".join(
        hypothesis_name({"node": leaf.rsplit(".", 1)[0], "conclusion": leaf.rsplit(".", 1)[1]})
        for leaf in leaves)
    solution = (
        LICENCE_HEADER
        + "".join(f"import {stem}\n" for stem in vendored)
        + f"""
/-!
# Solution: `{key}`

**Generated file** -- regenerated by `python scripts/ieantn.py spinoff {key}`.

The proof is `{node_id}.challenge_{cid}`, vendored from the node's solution project unchanged. This
file only renames it into the namespace the Challenge uses, which exists so that the compared name
does not collide with the sorried challenge the source repository generates for its own build.
-/

theorem {SPINOFF_NAMESPACE}.main{binders} :
    {statement} :=
  {node_id}.challenge_{cid}{(' ' + arguments) if arguments else ''}
""")
    (target / "Solution.lean").write_text(solution, encoding="utf-8", newline="\n")

    for path in solution_dir.glob("*.lean"):
        if path.name != "Solution.lean":
            (target / path.name).write_text(path.read_text(encoding="utf-8"),
                                            encoding="utf-8", newline="\n")
    vendor = solution_dir / "Solution.lean"
    (target / "NodeSolution.lean").write_text(vendor.read_text(encoding="utf-8"),
                                              encoding="utf-8", newline="\n")

    (target / "comparator.json").write_text(
        json.dumps({
            "challenge_module": "Challenge",
            "solution_module": "Solution",
            "theorem_names": [f"{SPINOFF_NAMESPACE}.main"],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        }, indent=2) + "\n", encoding="utf-8", newline="\n")

    (target / "lean-toolchain").write_text(
        (ROOT / "lean-toolchain").read_text(encoding="utf-8"), encoding="utf-8", newline="\n")
    for name in ("LICENSE", "LICENCE"):
        if (ROOT / name).is_file():
            (target / name).write_text((ROOT / name).read_text(encoding="utf-8"),
                                       encoding="utf-8", newline="\n")
            break
    else:
        print("warning: no LICENSE at the repository root; Palomar requires exactly one")

    inside = target.is_relative_to(ROOT)
    print(f"wrote {rel(target) if inside else target}")
    print("\nstill to do by hand, and deliberately not guessed at:")
    print("  1. lakefile.toml -- this needs a pinned git dependency on the source repository")
    print("  2. lake-manifest.json -- commit the one Lake resolves")
    print("  3. formalization.yaml -- start from the node's, drop `node` and `conclusions`, and")
    print("     add a limitation naming each hypothesis above")
    print("  4. validate: see the `palomar-submission` skill for running Palomar's own validator")
    if compile_check:
        # The Challenge imports Mathlib and nothing else, so this repository's own
        # environment can elaborate it as-is -- the assembled Lake project is not needed.
        # This is the check that the inlining is faithful rather than merely plausible.
        print("\nchecking the assembled Challenge elaborates...")
        built = subprocess.run(
            ["lake", "env", "lean", str(target / "Challenge.lean")],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
        noise = [line for line in (built.stdout + built.stderr).splitlines()
                 if "declaration uses" not in line and line.strip()]
        if built.returncode != 0 or noise:
            print("FAIL: the inlined Challenge does not compile cleanly")
            print("\n".join(noise[:20]))
            return False
        print("ok  the Challenge elaborates, with only the deliberate `sorry`")
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
    # Regenerate everything rather than writing this node's challenge alone: the umbrella is
    # generated too, and a scaffold that leaves it stale produces a node that quietly is not built.
    gen_challenges(check_only=False)

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
    # Every Lean file in the node, not just `Conclusions.lean`. A node may carry `Tables.lean`
    # and `Examples.lean` too, and copying only the conclusions left the new version silently
    # missing them -- which compiled, because the old version's copies were still there to satisfy
    # the imports, and so would have been noticed only when the old version was deleted.
    for name in ["formalization.yaml"] + sorted(
            path.name for path in latest.glob("*.lean") if path.name != "Challenge.lean"):
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


    gen_challenges(check_only=False)

    print(f"created {rel(target)} from {rel(latest)}")
    print("\nnext:")
    print(f"  1. edit {rel(target / 'Conclusions.lean')} -- this is the point of the new version")
    print("  2. python scripts/ieantn.py gen-challenges")
    print(f"  3. justify it: a solution, or a bridge from {old_id} under IEANTN/Bridges/")
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
    if replacement == node_id:
        print(f"error: `{node_id}` cannot supersede itself")
        return False
    if ((nodes[replacement].get("node") or {}).get("status")) == "deprecated":
        print(f"error: `{replacement}` is itself deprecated; name a live node")
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
    for name in (
        "check-closure", "check-graph", "check-pins", "check-receipts", "report", "housekeeping",
        "status", "check"
    ):
        sub.add_parser(name)
    generate = sub.add_parser("gen-challenges")
    generate.add_argument("--check", action="store_true", help="fail instead of rewriting")
    prints = sub.add_parser("fingerprint")
    prints.add_argument("--check", action="store_true", help="fail instead of rewriting")
    picture = sub.add_parser("graph")
    picture.add_argument("--check", action="store_true", help="fail instead of rewriting")
    per_node = sub.add_parser("pages")
    per_node.add_argument("--check", action="store_true", help="fail instead of rewriting")
    snapshot = sub.add_parser("state")
    snapshot.add_argument("--check", action="store_true", help="fail instead of rewriting")
    fresh = sub.add_parser("new-node")
    fresh.add_argument("family", help="e.g. FKS2")
    fresh.add_argument(
        "--kind", default="paper", choices=["paper", "pipeline", "folklore", "computation"]
    )
    spun = sub.add_parser("spinoff")
    spun.add_argument("conclusion", help="e.g. Lcm.v2.lcmUpto_not_highlyAbundant_of_primeGap")
    spun.add_argument("--out", required=True, help="directory to write the submission into")
    spun.add_argument("--compile", action="store_true", help="build the assembled project")
    version = sub.add_parser("new-version")
    version.add_argument("family", help="e.g. Lcm")
    changed = sub.add_parser("diff")
    changed.add_argument("--base", default="origin/main")
    solution = sub.add_parser("new-solution")
    solution.add_argument("node", help="e.g. Lcm.v1")
    written = sub.add_parser("record-receipt", help="verification workflow only")
    written.add_argument("node", help="e.g. Lcm.v1")
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
    if args.command == "check-pins":
        return 0 if check_pins() else 1
    if args.command == "check-receipts":
        return 0 if check_receipts() else 1
    if args.command == "gen-challenges":
        return 0 if gen_challenges(args.check) else 1
    if args.command == "state":
        return 0 if state(args.check) else 1
    if args.command == "fingerprint":
        return 0 if fingerprint(args.check) else 1
    if args.command == "report":
        return 0 if report() else 1
    if args.command == "status":
        return 0 if status() else 1
    if args.command == "diff":
        return 0 if diff(args.base) else 1
    if args.command == "new-solution":
        return 0 if new_solution(args.node) else 1
    if args.command == "record-receipt":
        return 0 if record_receipt(args.node, args.solution, args.run_url, args.stamp) else 1
    if args.command == "housekeeping":
        return 0 if housekeeping() else 1
    if args.command == "new-node":
        return 0 if new_node(args.family, args.kind) else 1
    if args.command == "graph":
        return 0 if graph(args.check) else 1
    if args.command == "pages":
        return 0 if pages(args.check) else 1
    if args.command == "spinoff":
        return 0 if spinoff(args.conclusion, args.out, args.compile) else 1
    if args.command == "new-version":
        return 0 if new_version(args.family) else 1
    if args.command == "deprecate":
        return 0 if deprecate(args.node, args.replacement) else 1
    if args.command == "check":
        return 0 if all(
            [check_closure(), check_graph(), check_pins(), check_receipts(online=False),
             gen_challenges(True), state(True), graph(True), pages(True)]
        ) else 1
    return 2


if __name__ == "__main__":
    sys.exit(main())
