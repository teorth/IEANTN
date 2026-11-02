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
    python scripts/ieantn.py state                   refresh STATE.md (a view; CI commits it)
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
import datetime
import hashlib
import json
import os
import pathlib
import re
import subprocess
import tempfile
import textwrap
import time
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
#: Retired location. Fingerprints now live one file per node, beside the `formalization.yaml`
#: they describe, so two pull requests touching different nodes cannot collide in one file.
#: Readers still fall back to this path, so `diff` can recover the state at a commit from before
#: the split without a special case for "old enough".
FINGERPRINTS = ROOT / "fingerprints.json"
#: What that per-node file is called, inside `IEANTN/Nodes/<Family>/<version>/`.
FINGERPRINTS_NAME = "fingerprints.json"
STATE = ROOT / "STATE.md"
GRAPH = ROOT / "GRAPH.md"
#: The same graph drawn, because Markdown can no longer hold it: GitHub renders Mermaid
#: through a sandboxed viewer that refuses a diagram over 50,000 characters, and the
#: conclusion-level graph passed that at 63,621. Laid out here rather than in the browser so
#: the file stays byte-for-byte reproducible, which is what lets CI diff it like the others.
GRAPH_PAGE = ROOT / "docs" / "graph.html"
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
#: The four values answer one question -- *has anyone worked out what this rests on, and could all
#: of it be drawn?*
#:
#: * `undetermined` -- nobody has looked. The default.
#: * `traced` -- the inputs are written down, and at least one of them is **not** an edge. Either
#:   it is not a node yet, or it can never be one: an algorithm, a data set, a computation. The
#:   justification note is where they are named.
#: * `identified` -- every input is drawn as an edge. Nothing is missing from the picture.
#: * `none` -- there are no inputs. A conditional whose hypotheses a consumer supplies, for
#:   instance.
#:
#: `traced` exists because `undetermined` was doing two jobs. "Nobody has looked at Platt2017" and
#: "Platt2017 rests on Theorem 4.2 of Trudgian, Whittaker-Shannon sampling, a subconvexity bound in
#: Lemma A.10, and its own FFT, of which only the third could currently be an edge" are not the
#: same state, and rendering them identically threw away the second one's work. It also lets
#: `identified` mean exactly what it says, instead of "identified, apart from the bits that cannot
#: be drawn, which are in a note".
#:
#: `none` is the third case and is not the same as `identified` with an empty list: it says someone
#: looked and there is genuinely nothing upstream. Lcm.v2 assumes its prime-gap input internally by
#: design; MT's Theorem 1 is unconditional. Having a word for that keeps the check from emitting a
#: warning nobody can ever act on, which is how warnings stop being read.
IMPORT_STATUSES = {"identified", "traced", "none", "undetermined"}
DEFAULT_IMPORT_STATUS = "undetermined"


def import_status(conclusion: dict) -> str:
    """Whether this conclusion's imports have been worked out. Absent means not."""
    return conclusion.get("imports_status") or DEFAULT_IMPORT_STATUS


#: A justification that stands on its own evidence.
PRIMITIVE_KINDS = {"lean-comparator", "lean-noncompliant", "numerical", "literature", "asserted",
                   "none-yet"}

#: A complete Lean proof that no receipt is available for. Two cases, which a reader of the views
#: need not distinguish: the proof uses an axiom Comparator does not permit -- `native_decide`
#: goes through `Lean.ofReduceBool` -- or the verification workflow cannot be run on it as it
#: stands, because of a dependency the network has not admitted to its trust base, or a build no
#: runner will finish. The proof is in this repository under `Solutions/`, where anyone may build
#: it; what is missing is our own certificate that it proves the challenge. So it is a leaf of the
#: trust graph -- what a reader relies on is the author's report that it builds and audits -- and
#: it is kept apart from `none-yet` because "nobody has written a proof" and "the proof is written
#: and we have not certified it" call for entirely different work.
NONCOMPLIANT_KIND = "lean-noncompliant"
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
    "inactive",              # retired without a successor: kept on disk, out of the build and graph
}

#: A node that was built to support another and ended up unused. Unlike `deprecated`, which marks a
#: node superseded by a newer version and changes nothing mechanically, `inactive` takes the node out
#: of the network altogether: `load_nodes` leaves it out, so the core build, the graph, STATE, the
#: pages, the fingerprints and housekeeping all stop seeing it. Its files stay where they are, so
#: `reactivate` is a status change and a regeneration rather than an archaeology project.
INACTIVE = "inactive"

IMPORT_RE = re.compile(
    r"^[ \t]*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)",
    re.MULTILINE,
)

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
    global GRAPH_PAGE
    global RECEIPTS, CHANGES, SOLUTIONS
    ROOT = path
    NODES_DIR = ROOT / "IEANTN" / "Nodes"
    VOCAB_DIR = ROOT / "IEANTN" / "Vocabulary"
    BRIDGES_DIR = ROOT / "IEANTN" / "Bridges"
    PAGES = ROOT / "docs" / "nodes"
    FINGERPRINTS = ROOT / "fingerprints.json"
    STATE = ROOT / "STATE.md"
    GRAPH = ROOT / "GRAPH.md"
    GRAPH_PAGE = ROOT / "docs" / "graph.html"
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


#: Why a stale derived view is a warning rather than a failure. `STATE.md`, `GRAPH.md` and the
#: pages under `docs/nodes/` are written by `.github/workflows/derived.yml` on every push to
#: `main`, and by nobody else. They carry no information that is not in the yaml, so a pull
#: request that regenerated them added nothing to review -- and guaranteed a conflict with every
#: other open pull request, since every one of them rewrites the same few files. CI is the single
#: writer precisely so that those conflicts cannot happen.
DERIVED_NOTE = (
    "out of date. This is a view, regenerated on `main` by .github/workflows/derived.yml; "
    "a pull request does not need to include it. `python scripts/ieantn.py {command}` "
    "refreshes it locally."
)


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


def _char_literal_length(text: str, index: int) -> int:
    """Length of a Lean character literal at `index`, or 0 if this quote is not one.

    A name suffix (`Nat.succ'`) is not a literal. `'a'` and `'\\n'` are. Getting this wrong in
    either direction lets a quote swallow the next import or invent a comment delimiter.
    """
    if index and (text[index - 1].isalnum() or text[index - 1] in "_'"):
        return 0
    if index + 2 < len(text) and text[index + 1] != "\\" and text[index + 2] == "'":
        return 3
    if index + 3 < len(text) and text[index + 1] == "\\" and text[index + 3] == "'":
        return 4
    return 0


def strip_lean_comments(text: str) -> str:
    """Lean source with `--` line comments and nested `/- -/` blocks removed.

    Needed because a plain search for `sorry` also matches the word in prose. The docstring of an
    Examples file explaining *why* it may not contain `sorry` is not a `sorry`, and a check that
    cannot tell the difference is worse than none: it trains people to work around it.

    String and character literals are blanked, not scanned. A `/-` or `--` inside `"..."` is text,
    and treating it as a comment delimiter hides whatever follows -- including a real import --
    until a later `-/` that was never opened. The word `sorry` inside a string is not a hole.
    """
    out: list[str] = []
    index, depth, length = 0, 0, len(text)

    def blank_string() -> None:
        nonlocal index
        out.append(" ")
        index += 1
        while index < length:
            if text[index] == "\\" and index + 1 < length:
                out.append("  ")
                index += 2
                continue
            if text[index] == '"':
                out.append(" ")
                index += 1
                return
            out.append("\n" if text[index] == "\n" else " ")
            index += 1

    while index < length:
        if depth == 0 and text[index] == '"':
            blank_string()
            continue
        if depth == 0 and text[index] == "'":
            width = _char_literal_length(text, index)
            if width:
                out.append(" " * width)
                index += width
                continue
        if text.startswith("/-", index):
            out.append("  ")
            depth += 1
            index += 2
        elif depth and text.startswith("-/", index):
            out.append("  ")
            depth -= 1
            index += 2
        elif depth:
            # Comments are whitespace: preserve token boundaries and line starts.
            out.append("\n" if text[index] == "\n" else " ")
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


def is_inactive(node: dict) -> bool:
    return (node.get("node") or {}).get("status") == INACTIVE


def load_nodes(include_inactive: bool = False) -> dict[str, dict]:
    """node id -> parsed formalization.yaml, with the directory recorded under '_dir'.

    Inactive nodes are left out unless asked for. That one filter is what takes a deactivated node
    out of the network: the umbrella, check-graph, the fingerprints, STATE, GRAPH, the pages,
    housekeeping and status all start here, so none of them has to know the status exists.
    """
    nodes: dict[str, dict] = {}
    for directory in node_dirs():
        data = yaml.safe_load((directory / "formalization.yaml").read_text(encoding="utf-8")) or {}
        data["_dir"] = directory
        if include_inactive or not is_inactive(data):
            nodes[node_id_of(directory)] = data
    return nodes


def duplicate_keys(text: str) -> list[tuple[str, str, int]]:
    """Every key written twice in one mapping: `(containing path, key, line)`.

    A duplicate key is the one metadata error that reads as success. PyYAML keeps the last
    occurrence, so an edit that adds a key some later duplicate overrides changes nothing at all
    and every check here goes on passing -- which is how `imports_status: traced` sat unapplied on
    `FKS.v1` from one pull request to the next. ruamel, which every mutating command goes through,
    refuses such a file outright with a `DuplicateKeyError`, so the same duplicate also breaks
    `new-version`, `deprecate`, `deactivate`, `progress --write` and the step that records a
    receipt. Neither half of that is visible from reading the file, and the two halves disagree
    about what the file even says.

    Composed rather than constructed: the node graph keeps the source positions, and nothing has
    to be built to find a repeat.
    """
    found: list[tuple[str, str, int]] = []

    def walk(node: yaml.Node, path: str) -> None:
        if isinstance(node, yaml.MappingNode):
            seen: set[str] = set()
            for key, value in node.value:
                name = str(getattr(key, "value", key))
                if name in seen:
                    found.append((path or "the document", name, key.start_mark.line + 1))
                seen.add(name)
                walk(value, f"{path}.{name}" if path else name)
        elif isinstance(node, yaml.SequenceNode):
            for index, item in enumerate(node.value):
                walk(item, f"{path}[{index}]")

    root = yaml.compose(text, Loader=yaml.SafeLoader)
    if root is not None:
        walk(root, "")
    return found


def inactive_nodes() -> dict[str, dict]:
    return {k: v for k, v in load_nodes(include_inactive=True).items() if is_inactive(v)}


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
        toolchain_path = ROOT / "lean-toolchain"
        if not toolchain_path.is_file():
            problems.add(rel(ROOT), "has no `lean-toolchain`, so the verification pin cannot be checked")
            return problems.report("verification pins")
        current = toolchain_path.read_text(encoding="utf-8").strip()
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
        receipt = load_receipt(path.stem)
        if receipt is None:
            problems.add(rel(path), "receipt is unreadable or has an invalid JSON object shape")
            continue
        url = (receipt.get("run") or {}).get("workflow_run", "")
        match = RUN_URL_RE.match(url) if isinstance(url, str) else None
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
        if jobs.returncode != 0:
            problems.add(rel(path),
                         f"run {run_id} jobs could not be read: {jobs.stderr.strip()}")
            continue
        names = jobs.stdout.split("\n")
        if any("(" in name for name in names) and not any(f"({node_of})" in name for name in names):
            problems.add(
                rel(path),
                f"run {run_id} verified {[n for n in names if '(' in n]}, not `{node_of}`",
            )

    return problems.report("receipt provenance")


def repository_slug() -> str | None:
    """`owner/name` for `origin`, or None if there is no usable remote."""
    remote = subprocess.run(
        ["git", "remote", "get-url", "origin"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
    ).stdout.strip()
    return re.sub(r"^.*github\.com[:/]|\.git$", "", remote) if remote else None


def _gh_json(args: list[str]) -> str:
    finished = subprocess.run(["gh", *args], cwd=ROOT, capture_output=True, text=True,
                              encoding="utf-8")
    return finished.stdout.strip() if finished.returncode == 0 else ""


def remote_branch_sha(branch: str) -> str | None:
    """The tip of `branch` on `origin`, or `None` if `origin` has no such branch."""
    finished = subprocess.run(
        ["git", "ls-remote", "--heads", "origin", branch],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if finished.returncode != 0:
        return None
    for line in (finished.stdout or "").splitlines():
        sha, _, ref = line.partition("	")
        if ref.strip() == f"refs/heads/{branch}":
            return sha.strip()
    return None


def similar_branches(branch: str) -> list[str]:
    """Remote branches whose names contain, or are contained in, `branch`.

    A dropped path prefix -- `foo` for `node/foo` -- is the failure this is for, and it is not
    hypothetical: a verification was dispatched for `fks2-corollary-22` when the branch was
    `node/fks2-corollary-22`, and the run burned an approval to die at checkout.
    """
    finished = subprocess.run(
        ["git", "ls-remote", "--heads", "origin"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if finished.returncode != 0:
        return []
    names = [line.partition("	")[2].strip().removeprefix("refs/heads/")
             for line in (finished.stdout or "").splitlines()]
    return [n for n in names if n and (branch in n or n in branch) and n != branch]


def local_head_sha() -> str | None:
    finished = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                              capture_output=True, text=True, encoding="utf-8")
    return (finished.stdout or "").strip() if finished.returncode == 0 else None


def branch_for_pr(pr: int) -> str | None:
    """Resolve a pull request to a branch on `origin` that `verify.yml` can check out.

    `verify.yml` takes a branch name and both reads and writes it on THIS repository: the receipt
    job checks out `inputs.branch` and pushes the receipt back to `refs/heads/$BRANCH`. A pull
    request from a fork has no such branch, so verifying one used to mean doing this by hand, and
    the first time anybody tried it the dispatch failed the branch-existence guard with no hint
    that a fork was the reason.

    For a same-repository pull request there is nothing to do but read the name off it. For a fork,
    the head is copied to a branch of the same name here. The commit is obtained through
    `refs/pull/<n>/head`, which GitHub publishes on the BASE repository, so this needs no remote
    for the contributor's fork and no push access to it -- which is just as well, since pushing to
    someone else's repository is a different kind of act from pushing to your own.
    """
    fields = _gh_json(["pr", "view", str(pr), "--json",
                       "headRefName,headRefOid,isCrossRepository,state,headRepositoryOwner",
                       "--jq", "[.state, .headRefName, .headRefOid, "
                               "(.isCrossRepository|tostring), .headRepositoryOwner.login] | @tsv"])
    if not fields:
        print(f"error: cannot read pull request #{pr}")
        return None
    state, ref, sha, cross, owner = (fields.split("\t") + [""] * 5)[:5]
    if state != "OPEN":
        print(f"error: pull request #{pr} is {state.lower()}, so there is nothing to verify")
        return None

    if cross != "true":
        print(f"#{pr} is a branch on this repository: verifying `{ref}` directly")
        return ref

    existing = remote_branch_sha(ref)
    if existing == sha:
        print(f"#{pr} is from {owner}'s fork; `{ref}` here already matches its head")
        return ref

    # Fetch through the base repository's own pull ref rather than the fork.
    fetched = subprocess.run(["git", "fetch", "origin", f"refs/pull/{pr}/head"],
                             cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if fetched.returncode != 0:
        print(f"error: could not fetch refs/pull/{pr}/head: {(fetched.stderr or '').strip()}")
        return None

    if existing is not None:
        print(f"warning: `{ref}` already exists here at {existing[:8]} and #{pr} is at {sha[:8]};")
        print("         refusing to move it. Delete it, or verify it as it stands with --branch.")
        return None

    print(f"#{pr} is from {owner}'s fork; copying its head to `{ref}` here so the receipt has")
    print("  somewhere to land. Nothing is written to the fork.")
    pushed = subprocess.run(["git", "push", "origin", f"{sha}:refs/heads/{ref}"],
                            cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if pushed.returncode != 0:
        print(f"error: could not create `{ref}` on origin: {(pushed.stderr or '').strip()}")
        return None
    return ref


def report_pr_followup(pr: int, branch: str) -> None:
    """Say where the receipt went, because it is not where someone would look for it.

    The receipt lands on the branch here, NOT on the contributor's pull request, so #<pr> still
    shows the pre-verification state and merging it would merge a node with no receipt. Both ways
    out are worth printing: whichever is taken, GitHub tends to mark the original CLOSED rather
    than MERGED, and a first-time contributor reading their own pull request cannot tell from that
    badge that their work was accepted.
    """
    print()
    print("=" * 72)
    print(f"  THE RECEIPT IS ON `{branch}` HERE, NOT ON #{pr}.")
    print(f"  Merging #{pr} as it stands would merge the node without its receipt.")
    print()
    print("  Either push the receipt into the fork, if the contributor allowed edits:")
    print(f"    git fetch origin {branch}")
    print(f"    git push <their-remote> FETCH_HEAD:{branch}")
    print(f"  or open a pull request from `{branch}` and merge that instead:")
    print(f"    gh pr create --head {branch} --title '<node>: verified'")
    print()
    print(f"  The second closes #{pr} automatically only if its head is an ancestor, and GitHub")
    print("  marks it CLOSED rather than MERGED either way. Say so in a comment -- the badge")
    print("  understates what happened, and the contributor has no other way to tell.")
    print("=" * 72)


def verify(node: str, branch: str, dispatch: bool, precheck: bool = True,
           pr: int | None = None) -> bool:
    """Dispatch `verify.yml` and follow it, making the approval gate impossible to miss.

    This exists because `gh run watch` draws a run that has not started identically to one that is
    building: a spinner and a job name. A verification sits at the `verification` environment gate
    until a maintainer approves it, and the difference is plainly visible in the API -- `status` is
    `waiting` and no step has run -- but nothing surfaces it. Someone once waited thirty-two
    minutes for a run that had executed nothing at all.

    It cannot approve anything, and must not be able to. Approval is the one privileged act in this
    repository, and the gate exists precisely because a human is supposed to have looked at the
    branch. All this does is refuse to draw a progress spinner over a request for attention.
    """
    repository = repository_slug()
    if not repository:
        print("no `origin` remote; cannot find the run")
        return False

    if dispatch:
        # Two guards before spending someone's approval. A dispatch that cannot succeed is not
        # free: the gate exists so that a human looks at the branch, and an hour of compute follows.
        sha = remote_branch_sha(branch)
        if sha is None:
            print(f"error: `origin` has no branch `{branch}`, so the workflow would fail at")
            print("       checkout -- after the approval had already been given.")
            near = similar_branches(branch)
            if near:
                print("       Did you mean:")
                for name in near[:5]:
                    print(f"         {name}")
            return False

        if precheck:
            head = local_head_sha()
            if head != sha:
                print(f"warning: local HEAD is not the tip of `{branch}` on origin, so the")
                print("         solution cannot be checked from here. Dispatching unchecked;")
                print("         if Comparator rejects it, that is the first you will hear.")
            else:
                result = solution_holes(node)
                if result is None:
                    print(f"error: no solution under {rel(SOLUTIONS / node)} to verify")
                    return False
                built, holes, proved = result
                if not built:
                    print(f"error: {node}'s solution does not typecheck; Comparator would reject it")
                    return False
                unproved = sorted(name for name, ok in (proved or {}).items() if not ok)
                if holes or unproved:
                    print(f"error: {node} is not ready. Comparator would reject it, and the run")
                    print("       costs an approval and up to an hour of compute.")
                    for hole in holes:
                        print(f"         hole   {hole}")
                    for name in unproved:
                        print(f"         OPEN   {name}")
                    print("       A node is verified all at once or not at all -- `record-receipt`")
                    print("       refuses unless `comparator.json` covers every conclusion. Close")
                    print("       the holes, or split the node across versions (docs/NODES.md).")
                    print("       Re-run with --skip-precheck to dispatch anyway.")
                    return False

        started = subprocess.run(
            ["gh", "workflow", "run", "verify.yml", "-f", f"node={node}", "-f", f"branch={branch}"],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
        if started.returncode != 0:
            print(f"dispatch failed: {started.stderr.strip()}")
            return False
        print(f"dispatched verify.yml for {node} on {branch}")
        time.sleep(5)

    run_id = _gh_json(["run", "list", "--workflow=verify.yml", "--limit", "1",
                       "--json", "databaseId", "--jq", ".[0].databaseId"])
    if not run_id:
        print("no verification run found")
        return False
    url = f"https://github.com/{repository}/actions/runs/{run_id}"

    announced = False
    while True:
        status = _gh_json(["api", f"repos/{repository}/actions/runs/{run_id}",
                           "--jq", "[.status, .conclusion] | @tsv"]).split("\t")
        state, conclusion = (status + ["", ""])[:2]

        if state == "waiting":
            if not announced:
                print()
                print("=" * 72)
                print("  WAITING FOR YOUR APPROVAL -- nothing is running yet.")
                print()
                print(f"    {url}")
                print("    Review deployments -> verification -> Approve and deploy")
                print()
                print("  Approving means vouching for this branch's core Lean, not its solution:")
                print("  the receipt job runs `lake build` on it while holding a write token.")
                print("=" * 72)
                print()
                announced = True
        elif state == "completed":
            print(f"run {run_id} completed: {conclusion}")
            print(f"  {url}")
            if conclusion == "success":
                if pr is not None:
                    report_pr_followup(pr, branch)
                else:
                    print("  the receipt is on the branch; open a pull request for it")
            return conclusion == "success"
        else:
            jobs = _gh_json(["api", f"repos/{repository}/actions/runs/{run_id}/jobs",
                             "--jq", r'.jobs[] | "\(.name): \(.status)"'])
            print(f"[{state}] " + " | ".join(jobs.split("\n")) if jobs else f"[{state}]")
        time.sleep(20)


PROGRESS_STATES = {"in-progress", "stalled", "abandoned"}


def solution_holes(node: str) -> tuple[bool, list[str], dict[str, bool]] | None:
    """Build `Solutions/<node>` and report where it is incomplete.

    Returns `(built, holes, proved)` — whether it typechecks at all, the `file:line` of every
    declaration that uses `sorry`, and for each compared theorem whether it is genuinely proved.

    The last of those is the one that matters, and it is why this does not simply grep for the word
    `sorry`. A declaration can contain no `sorry` and still not be proved, because something it
    depends on has one; `#print axioms` sees that and a text search does not. It is also what
    Comparator will check, so this is a cheap local preview of the verdict — minus the sandbox, the
    second kernel, and the receipt, none of which this can or should substitute for.
    """
    directory = SOLUTIONS / node
    if not (directory / "lakefile.toml").is_file() and not (directory / "lakefile.lean").is_file():
        return None

    # SAY WHAT IS ABOUT TO HAPPEN. A solution is a separate Lake project and shares nothing with
    # the core build, so the first build of a new one compiles its OWN Mathlib -- minutes with a
    # cache, hours without -- and `capture_output` below emits not one line while it does. That was
    # reported as a hang, which is fair: silence and a wedge look identical from outside. It is the
    # same defect `verify` exists to prevent, one layer down, so it gets the same treatment.
    warm = (directory / ".lake" / "packages" / "mathlib" / ".lake" / "build").is_dir()
    print(f"  building {rel(directory)}, which may take a while", flush=True)
    if not warm:
        print("    no build tree there yet, so this builds the solution's own Mathlib first.",
              flush=True)
        print("    `lake exe cache get` in that directory first makes it minutes, not hours;",
              flush=True)
        print("    `--skip-precheck` dispatches without it.", flush=True)
    built = subprocess.run(["lake", "build"], cwd=directory, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
    if built.returncode != 0:
        # It does not typecheck at all, which is a different and worse state than having holes.
        return (False, [], {})

    config = directory / "comparator.json"
    settings = json.loads(config.read_text(encoding="utf-8"))
    names = settings.get("theorem_names") or []

    # The holes are counted by re-elaborating, NOT from the `lake build` above. Lean emits
    # `declaration uses 'sorry'` only when it actually compiles a file, so on an up-to-date build
    # the warnings are simply absent and a count taken from them silently reads zero -- which is
    # exactly what this reported the first time it was run against a scaffolded solution with three
    # open goals. `lake env lean` re-elaborates and always emits them.
    # Every top-level file, not just the compared one. A solution is split across files for build
    # time -- see docs/SOLUTIONS.md -- so the holes are usually in a sibling, and elaborating only
    # the root reports zero while three theorems are plainly open. That is what this did first.
    holes: list[str] = []
    for source in sorted(directory.glob("*.lean")):
        # Lake already elaborated its configuration during the successful build above.
        # Its DSL commands are not available to an ordinary `lake env lean` proof probe.
        if source.name == "lakefile.lean":
            continue
        fresh = subprocess.run(["lake", "env", "lean", source.name], cwd=directory,
                               capture_output=True, text=True, encoding="utf-8", errors="replace")
        seen_output = (fresh.stdout or "") + (fresh.stderr or "")
        # An elaboration that FAILED emits no `declaration uses` warnings, so scanning only for
        # those reads a failure as "no holes" -- the same silent zero this whole routine exists to
        # avoid, one level up. Seen in practice: a transient `failed to read file ...olean.private`
        # on Windows turned four open goals into a clean bill of health, and `--write` would have
        # recorded `remaining_holes: 0` on the node. Treat it as unbuildable instead.
        if fresh.returncode != 0 or re.search(r"^error:|: error:", seen_output, re.MULTILINE):
            print(f"  re-elaborating {source.name} failed, so its holes cannot be counted:")
            for line in seen_output.splitlines()[:3]:
                # Lean's output carries goal characters like U+22A2 that a cp1252 console cannot
                # encode, and an uncaught UnicodeEncodeError here would replace a useful diagnostic
                # with a traceback. Report is best-effort; the exit status is what matters.
                print("    " + line.encode("ascii", "replace").decode("ascii"))
            return (False, [], {})
        holes += [
            f"{pathlib.PurePosixPath(m.group(1)).name}:{m.group(2)}"
            for m in re.finditer(r"([^\s:]+):(\d+):\d+: warning: declaration uses", seen_output)
        ]
    holes = sorted(set(holes))
    if not names:
        return (True, holes, {})

    # Use an exclusive temporary file: a contributor may already have a scratch file named
    # `_ieantn_axioms.lean`, and a progress report must never overwrite or delete it.
    with tempfile.NamedTemporaryFile(mode="w", prefix="_ieantn_axioms_", suffix=".lean",
                                     dir=directory, encoding="utf-8", delete=False) as handle:
        probe = pathlib.Path(handle.name)
    try:
        module = settings.get("solution_module") or "Solution"
        probe.write_text(f"import {module}\n"
                         + "".join(f"#print axioms {name}\n" for name in names),
                         encoding="utf-8", newline="\n")
        checked = subprocess.run(["lake", "env", "lean", probe.name], cwd=directory,
                                 capture_output=True, text=True, encoding="utf-8",
                                 errors="replace")
    finally:
        probe.unlink(missing_ok=True)
    seen = (checked.stdout or "") + (checked.stderr or "")
    if checked.returncode != 0:
        print("  the axiom probe failed; progress cannot be recorded until it succeeds")
        return (False, [], {})
    records = axiom_records(seen, names)
    proved = {name: (name in records and "sorryAx" not in records[name]) for name in names}
    return (True, holes, proved)


def axiom_records(output: str, names: list[str]) -> dict[str, str]:
    """Join each `#print axioms` report back into one string, per declaration.

    `#PRINT AXIOMS WRAPS`, and reading only the line that starts with the declaration name is
    therefore wrong. Lean pretty-prints the axiom list at the usual width, so a long name pushes
    the tail onto continuation lines:

        'Family.v2.challenge_some_rather_long_conclusion_name' depends on axioms: [propext,
         sorryAx,
         Classical.choice,
         Quot.sound]

    A single-line check misses `sorryAx` here -- and note WHEN it misses it: adding `sorryAx` to
    the list is itself part of what pushes the line over the width, so the failure mode is to
    report an unproved theorem as proved, which is the only direction that matters. That happened:
    a solution whose sole compared theorem was a bare `sorry` was reported as free of `sorryAx`,
    by the routine whose entire purpose is to preview Comparator's verdict.

    A record runs from the line beginning with the quoted name until the brackets balance, which
    also handles `'foo' does not depend on any axioms` -- no brackets, so it closes at once.
    """
    records: dict[str, str] = {}
    current: str | None = None
    for raw in output.splitlines():
        started = next((n for n in names if raw.startswith(f"'{n}'")), None)
        if started is not None:
            current = started
            records[current] = raw.rstrip()
        elif current is not None:
            records[current] += " " + raw.strip()
        if current is not None and records[current].count("[") == records[current].count("]"):
            current = None
    return records


def progress(node: str, write: bool) -> bool:
    """Report how far a solution has got, and optionally record it.

    `CONTRIBUTING.md` asks for a `progress` block carrying `remaining_holes`. Hand-maintaining that
    number is the silent-drift defect this repository keeps meeting, so `--write` derives it from
    the build instead.
    """
    nodes = load_nodes()
    if node not in nodes:
        print(f"no such node: {node}")
        return False
    result = solution_holes(node)
    if result is None:
        print(f"{node}: no solution under {rel(SOLUTIONS / node)}")
        return False
    built, holes, proved = result

    if not built:
        print(f"{node}: does NOT typecheck -- this is worse than having holes, and nothing below")
        print("  can be trusted until it builds. Run `lake build` in the solution to see why.")
        return False

    # A `progress.yaml` is prose for humans and deliberately unconstrained -- see docs/SOLUTIONS.md,
    # which says so. But one that is not valid YAML is one nobody and nothing can read, and it fails
    # silently precisely because nothing enforces it. This checks that it parses and nothing more:
    # no schema, no required fields. (Found the hard way: FKS2.v1's plan never parsed from the day
    # it was written.)
    plan = SOLUTIONS / node / "progress.yaml"
    if plan.exists():
        try:
            yaml.safe_load(plan.read_text(encoding="utf-8"))
        except yaml.YAMLError as exc:
            mark = getattr(exc, "problem_mark", None)
            where = f" at line {mark.line + 1}" if mark else ""
            print(f"  WARNING: {rel(plan)} is not valid YAML{where} -- {getattr(exc, 'problem', exc)}")
            print("    The plan is unconstrained by design, but an unparseable one is unreadable.")
            print("    Usual cause: a multi-line plain scalar containing `: `, or one indented level")
            print("    with its own key. Use a `>-` block scalar.")

    complete = proved and all(proved.values())
    print(f"{node}: typechecks, {len(holes)} declaration(s) using `sorry`")
    for hole in holes:
        print(f"  hole   {hole}")
    for name, ok in sorted(proved.items()):
        print(f"  {'proved' if ok else 'OPEN  '} {name}")
    if complete:
        print("  every compared theorem is free of `sorryAx`. Comparator is the next step;")
        print("  this is a preview of its verdict, not a substitute for it, and justifies nothing.")

    if not write:
        return True

    path = NODES_DIR / node.replace(".", "/") / "formalization.yaml"
    writer, data = edit_yaml(path)
    touched = 0
    for conclusion in conclusions_of(data):
        if conclusion.get("declaration") and not any(
                j.get("kind") in VERIFIED_KINDS for j in conclusion.get("justifications") or []):
            conclusion["progress"] = {
                "solution": f"Solutions/{node}/",
                "state": "in-progress",
                "remaining_holes": len(holes),
            }
            touched += 1
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        writer.dump(data, handle)
    print(f"  recorded remaining_holes: {len(holes)} on {touched} conclusion(s)")
    return True


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
        if not any((directory / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
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

    # An inactive node is out of the umbrella, so nothing compiles it -- unless something live
    # imports one of its modules, which would quietly pull it back into the core build. The
    # yaml-level edge is caught by check-graph; this is the Lean-level one, which the yaml never sees.
    retired = sorted(inactive_nodes())
    if retired:
        prefixes = [f"IEANTN.Nodes.{node_id}" for node_id in retired]
        live_files = [
            path
            for directory in node_dirs()
            if node_id_of(directory) not in retired
            for path in sorted(directory.glob("*.lean"))
        ] + sorted(BRIDGES_DIR.rglob("*.lean"))
        for path in live_files:
            for module in imports_of(path):
                if any(under(module, prefix) for prefix in prefixes):
                    problems.add(
                        rel(path),
                        f"imports `{module}`, which belongs to an inactive node. Reactivate the "
                        "node or drop the import: an inactive node is meant to be out of the build.",
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
    inactive = inactive_nodes()

    # Inactive nodes are out of the graph, but not out of review: the one thing asked of them is
    # to say why, since a directory nobody can account for is exactly what the status exists to
    # prevent.
    for node_id, node in sorted(inactive.items()):
        reason = (node.get("node") or {}).get("inactive_reason")
        if not isinstance(reason, str) or not reason.strip():
            problems.add(
                rel(node["_dir"] / "formalization.yaml"),
                f"`{node_id}` is inactive but gives no `node.inactive_reason`. Say why it was "
                "retired, so whoever finds the directory can tell whether to reactivate it.",
            )

    # Checked for every node, active or not, and before the early return below: a duplicate in an
    # inactive node's metadata is what would stop `reactivate` from writing it back.
    for node_id, node in sorted({**inactive, **nodes}.items()):
        path = node["_dir"] / "formalization.yaml"
        for container, key, line in duplicate_keys(path.read_text(encoding="utf-8")):
            problems.add(
                rel(path),
                f"line {line}: `{key}` is given twice in `{container}`. PyYAML keeps the last, so "
                "one of the two does nothing and every check here passes while the file says "
                "something nobody wrote; ruamel refuses the file, so the node-editing commands "
                "fail on it instead. Delete whichever is wrong.",
            )

    if not nodes:
        return problems.report("node graph (no active nodes)")

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

        # Two self-contradictions, both observed. Every FKS2-family node carried prose written
        # when it was a stub and never revisited -- one still said "no statement has been
        # transcribed from the paper" over four Comparator-verified conclusions, and one named
        # the wrong node in its own header. These files are the Palomar submission surface, so
        # stale prose here is a false statement to a registry rather than an untidy comment.
        # Neither check is a heuristic: each fires only when the file contradicts itself.
        text = (node["_dir"] / "formalization.yaml").read_text(encoding="utf-8")
        first = text.split("\n", 1)[0]
        if first.startswith("#") and node_id not in first:
            named = re.findall(r"`([A-Za-z0-9]+\.v[0-9]+)`", first)
            if named and node_id not in named:
                problems.add(where, f"the header comment says `{named[0]}`, not `{node_id}`")
        if conclusions_of(node) and "deliberately empty" in text:
            problems.add(
                where,
                f"still says `conclusions` is deliberately empty, with "
                f"{len(conclusions_of(node))} stated. Prose written for a stub has outlived it; "
                "read the whole file rather than only deleting the phrase.",
            )

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
                if kind == NONCOMPLIANT_KIND:
                    # The claim being made is that the code is here. A `lean-noncompliant`
                    # justification with no solution beside it is an `asserted` one wearing a
                    # borrowed coat.
                    solution = SOLUTIONS / node_id / "Solution.lean"
                    if not solution.is_file():
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: `{NONCOMPLIANT_KIND}` "
                            f"means the Lean proof is supplied, and {rel(solution)} is not there.",
                        )
                    if not str(justification.get("note") or "").strip():
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: `{NONCOMPLIANT_KIND}` "
                            "must say in `note` what stands between this proof and a receipt. "
                            "Without that, nobody can tell whether it still stands.",
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
                    elif (
                        not justification["bridge"].startswith("IEANTN/Bridges/")
                        or ".." in pathlib.PurePosixPath(justification["bridge"]).parts
                        or pathlib.PurePosixPath(justification["bridge"]).suffix != ".lean"
                        or not (ROOT / justification["bridge"]).resolve().is_relative_to(
                            BRIDGES_DIR.resolve()
                        )
                    ):
                        # A bridge outside the library is never compiled, so it would keep
                        # justifying its target after either statement moved out from under it.
                        problems.add(
                            where,
                            f"conclusion `{cid}`, justification `{jid}`: bridge file "
                            f"`{justification['bridge']}` must be a .lean file under "
                            "`IEANTN/Bridges/`, without parent-directory traversal, so "
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
                    "If someone looked and there are genuinely none, say `none`; if the inputs are "
                    "known but not all of them can be edges, say `traced`; if nobody has looked, "
                    "drop the field and let it read as undetermined.",
                )
            if status == "traced" and not (conclusion.get("justifications") or []):
                problems.add(
                    where,
                    f"conclusion `{cid}`: `imports_status: traced` means the inputs are written "
                    "down somewhere, and the only place for them is a justification note. With no "
                    "justification there is nowhere for the tracing to live.",
                )
            if status == "none" and (conclusion.get("imports") or []):
                problems.add(
                    where,
                    f"conclusion `{cid}`: `imports_status: none` but imports are listed.",
                )

            marker = conclusion.get("progress")
            if marker is not None:
                if not isinstance(marker, dict):
                    problems.add(where, f"conclusion `{cid}`: `progress` must be a mapping")
                else:
                    state = marker.get("state")
                    if state not in PROGRESS_STATES:
                        problems.add(
                            where,
                            f"conclusion `{cid}`: progress state `{state}` is not one of "
                            + ", ".join(sorted(PROGRESS_STATES)))
                    holes = marker.get("remaining_holes")
                    if holes is not None and not isinstance(holes, int):
                        problems.add(
                            where,
                            f"conclusion `{cid}`: `remaining_holes` must be a number -- derive it "
                            "with `ieantn.py progress <node> --write` rather than counting by hand")
                if designated_kind(conclusion) in VERIFIED_KINDS:
                    problems.add(
                        where,
                        f"conclusion `{cid}` carries both a `progress` marker and a verified "
                        "justification. `record-receipt` clears the marker; one left behind says "
                        "work is outstanding on something already done.")

            issue = conclusion.get("issue")
            if issue is not None and not isinstance(issue, int):
                problems.add(where, f"conclusion `{cid}`: `issue` must be a number, not `{issue}`")
            elif designated_kind(conclusion) == "none-yet" and issue is None:
                problems.warn(
                    where,
                    f"conclusion `{cid}` is unjustified and names no `issue`: nobody can claim "
                    "work nobody can find. Open an issue and record its number.",
                )
            elif designated_kind(conclusion) == NONCOMPLIANT_KIND and issue is None:
                problems.warn(
                    where,
                    f"conclusion `{cid}` designates `{NONCOMPLIANT_KIND}` and names no `issue`: "
                    "what stands between the proof and a receipt is tracked work. Open an issue "
                    "and record its number.",
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
                if target_node not in nodes and target_node in inactive:
                    problems.add(
                        where,
                        f"conclusion `{cid}` imports `{target_node}`, which is inactive and so "
                        "out of the build. Reactivate it (`python scripts/ieantn.py reactivate "
                        f"{target_node}`) or drop the edge.",
                    )
                    continue
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
    statements = json.loads(payload)
    if not isinstance(statements, dict) or set(statements) != set(declarations):
        sys.exit("error: ieantn_hash output does not cover exactly the requested conclusions")
    if not all(isinstance(text, str) for text in statements.values()):
        sys.exit("error: ieantn_hash returned a non-text statement")
    return {
        name: hashlib.sha256(text.encode("utf-8")).hexdigest()
        for name, text in statements.items()
    }


def fingerprints_path(directory: pathlib.Path) -> pathlib.Path:
    """Where one node's fingerprints live: beside its `formalization.yaml`."""
    return directory / FINGERPRINTS_NAME


def fingerprints_by_node(current: dict[str, str]) -> dict[pathlib.Path, dict[str, str]]:
    """Split a flat `declaration -> digest` map into one map per node directory.

    Keyed by directory, and every live node gets an entry: a node whose conclusions have all gone
    still needs its file rewritten to `{}` rather than left behind saying something false.
    """
    split: dict[pathlib.Path, dict[str, str]] = {}
    for node_id, node in load_nodes().items():
        prefix = f"{node_id}."
        split[node["_dir"]] = {
            name: digest for name, digest in current.items() if name.startswith(prefix)
        }
    return split


def fingerprint(check_only: bool) -> bool:
    """Maintain each node's `fingerprints.json`.

    Committing the fingerprints has a purpose beyond bookkeeping: it makes **every change of
    mathematical meaning show up as a diff line**, including ones whose Lean edit looks cosmetic.
    A reviewer can see that a statement moved without having to elaborate anything.

    One file per node, not one for the network. Nothing reads the digests as a whole, so a single
    file bought nothing and cost a conflict on every pair of branches that added a conclusion --
    every pair, since the file was sorted by name and both sides wrote into it. Sharded, two
    branches collide only when they touch the same node, which is a collision worth having.
    """
    current = compute_fingerprints()
    recorded = recorded_fingerprints()

    if not check_only:
        split = fingerprints_by_node(current)
        written = 0
        for directory, digests in sorted(split.items()):
            path = fingerprints_path(directory)
            text = json.dumps(digests, indent=2, sort_keys=True) + "\n"
            if (path.read_text(encoding="utf-8") if path.is_file() else None) != text:
                path.write_text(text, encoding="utf-8", newline="\n")
                written += 1
        if FINGERPRINTS.is_file():
            FINGERPRINTS.unlink()
            print(f"removed {rel(FINGERPRINTS)}: fingerprints are per node now")
        for name, digest in sorted(current.items()):
            marker = " " if recorded.get(name) == digest else "*"
            print(f"{marker} {digest[:16]}  {name}")
        print(f"\nwrote {written} of {len(split)} node fingerprint files")
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
    """The environment a verification run today would happen in.

    A missing toolchain file, or a manifest that is not an object, used to raise here. `status`
    and receipt grading both call this, so a bad checkout became a traceback instead of a stale
    or unknown environment.
    """
    manifest_path = ROOT / "lake-manifest.json"
    mathlib = None
    if manifest_path.is_file():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError):
            manifest = None
        packages = manifest.get("packages", []) if isinstance(manifest, dict) else []
        if isinstance(packages, list):
            mathlib = next(
                (
                    package.get("rev")
                    for package in packages
                    if isinstance(package, dict) and package.get("name") == "mathlib"
                ),
                None,
            )
    toolchain_path = ROOT / "lean-toolchain"
    toolchain = (
        toolchain_path.read_text(encoding="utf-8").strip() if toolchain_path.is_file() else None
    )
    return {
        "lean_toolchain": toolchain,
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
        receipt = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        return None
    if not isinstance(receipt, dict):
        return None
    for field in ("statement", "environment", "repository", "solution", "run"):
        if field in receipt and not isinstance(receipt[field], dict):
            return None
    for section, fields in (
        ("environment", ("lean_toolchain", "mathlib_rev")),
        ("repository", ("commit",)),
        ("solution", ("project",)),
        ("run", ("workflow_run",)),
    ):
        values = receipt.get(section, {})
        if any(values.get(field) is not None and not isinstance(values[field], str) for field in fields):
            return None
    return receipt


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


def assess(conclusion_key: str, receipt: dict, fingerprints: dict[str, str], *,
           consult_history: bool = True) -> tuple[str, str]:
    """Grade one receipt against the world as it is now.

    Two axes, deliberately not collapsed (ARCHITECTURE section 4):

    * a **statement** that has moved is a *broken edge* -- the verified implication no longer
      connects to what is now claimed. Binary and fatal, however small the edit;
    * an **environment** that has moved is ordinary staleness. Graduated, and expected.

    `consult_history` decides whether `churn` may be distinguished from `BROKEN`, and the views
    must pass `False`. Telling those apart means asking git whether a file changed since the
    receipt's commit, and a generated view that depends on git history is not reproducible: CI
    checks out a shallow tree where the commit is unreachable, grades `BROKEN` where a full clone
    grades `churn`, and `pages` then differs from what is committed. `status` is run by a human in
    a real clone and does ask.
    """
    recorded = receipt.get("statement") or {}
    if conclusion_key not in recorded:
        return "BROKEN", f"receipt records no fingerprint for `{conclusion_key}`"
    commit = (receipt.get("repository") or {}).get("commit")
    churn: str | None = None
    for name, digest in sorted(recorded.items()):
        now = fingerprints.get(name)
        if now is None:
            return "BROKEN", f"`{name}` no longer exists"
        if now != digest:
            which = "its own statement" if name == conclusion_key else f"`{name}`"
            # A fingerprint is a digest of the ELABORATED statement, so a Mathlib bump can move it
            # with the Lean source untouched -- a renamed instance is enough. That is not a severed
            # edge and must not be graded as one, or every bump manufactures BROKEN edges that look
            # like someone quietly rewrote a theorem. When the source is demonstrably unchanged the
            # verdict is `churn`; when it changed, or cannot be checked, it stays BROKEN.
            if consult_history and statement_source_unchanged(name, commit):
                churn = churn or (
                    f"{which} re-elaborates differently under the current environment, though its "
                    "Lean source is unchanged since verification"
                )
                continue
            return "BROKEN", f"{which} changed since verification"
    if churn is not None:
        return "churn", churn

    environment = receipt.get("environment") or {}
    current = current_environment()
    if (environment.get("mathlib_rev") == current["mathlib_rev"]
            and environment.get("lean_toolchain") == current["lean_toolchain"]):
        return "green", "verified against the current environment"

    recorded_toolchain = environment.get("lean_toolchain", "?")
    distance = release_distance(recorded_toolchain, current["lean_toolchain"])
    detail = environment_gap(environment, current)
    if distance is not None and distance > CACHE_WINDOW_RELEASES:
        return "orange", f"{detail} ({distance} releases; likely outside the cache window)"
    return "yellow", detail


def environment_gap(recorded: dict, current: dict) -> str:
    """Say which part of the environment moved, rather than always naming the toolchain.

    The message used to report only the *toolchain*. A Mathlib bump
    that keeps the toolchain therefore printed `verified under v4.34.0-rc2, now v4.34.0-rc2` --
    the same string twice, which reads as a bug in this script rather than as a stale receipt, and
    hides the revision that actually moved. Every conclusion verified before the September 2026
    bump said exactly that.

    So name whichever fields differ. The toolchain is still worth printing when it moved, because
    it is what `release_distance` grades and what governs the cache window.
    """
    parts = []
    if recorded.get("mathlib_rev") != current.get("mathlib_rev"):
        was = (recorded.get("mathlib_rev") or "?")[:12]
        now = (current.get("mathlib_rev") or "?")[:12]
        parts.append(f"Mathlib {was} -> {now}")
    if recorded.get("lean_toolchain") != current.get("lean_toolchain"):
        parts.append(f"toolchain {recorded.get('lean_toolchain', '?')} -> "
                     f"{current.get('lean_toolchain', '?')}")
    if not parts:
        # Reachable only if the caller's test and this one disagree; say so rather than inventing.
        return "verified under an environment that differs in some unrecorded way"
    return "verified under " + ", ".join(parts)


def statement_source_unchanged(conclusion_name: str, commit: str | None) -> bool:
    """Whether a conclusion's `Conclusions.lean` is untouched since the verified commit.

    This is what separates a Mathlib bump from a rewritten theorem. Both move a fingerprint, since
    the digest is taken of the *elaborated* statement; only one of them means the verified
    implication no longer reaches what the node claims.

    Deliberately conservative. It answers `True` only when git can be asked and says the file did
    not change: no `repository.commit` (schema 1 receipts), a commit missing locally, or a failed
    `git` call all give `False`, so an unanswerable question grades as `BROKEN` rather than as
    churn. Being wrong in that direction costs a re-verification; being wrong in the other hides a
    severed edge.
    """
    if not commit:
        return False
    node_id, _, _ = conclusion_name.rpartition(".")
    family, _, version = node_id.partition(".")
    if not family or not version:
        return False
    path = f"IEANTN/Nodes/{family}/{version}/Conclusions.lean"
    known = subprocess.run(
        ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if known.returncode != 0:
        return False
    # Local imported definitions can change a statement's meaning while this
    # Conclusions file stays untouched. Only an unchanged import closure lets
    # a moved fingerprint be attributed to the external environment.
    pending = [ROOT / path]
    sources: set[pathlib.Path] = set()
    while pending:
        source = pending.pop()
        if source in sources:
            continue
        if not source.is_file():
            return False
        sources.add(source)
        pending.extend(
            ROOT / (module.replace(".", "/") + ".lean")
            for module in imports_of(source) if under(module, "IEANTN")
        )
    changed = subprocess.run(
        ["git", "diff", "--name-only", commit, "--", *sorted(rel(p) for p in sources)],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if changed.returncode != 0:
        return False
    return not [line for line in changed.stdout.splitlines() if line.strip()]


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
    return drift_note(project, commit, files)


def drift_note(project: str, commit: str, files: list[str]) -> str:
    """Phrase the drift, naming the files and saying whether any of them is Lean.

    `changed in 1 file(s)` was true and useless: it sent the reader to `git diff` to find out
    whether the receipt had been undermined or a comment retyped. The Mathlib bump made that
    concrete -- afterwards EVERY verified solution reported exactly that line, and in every case the
    single file was `lake-manifest.json`.

    That is not nothing: the manifest fixes which Mathlib the solution builds against, so the
    receipt really does attest to a different environment, and the receipt's own
    `environment.mathlib_rev` is the thing to compare. But it is a different situation from a proof
    having been edited, and the two deserve different reactions from whoever reads the line. So the
    note says which files moved and whether any Lean source is among them, and stops short of
    grading it -- deciding what a manifest-only drift is worth is a judgement, not a computation.
    """
    names = sorted({pathlib.PurePosixPath(name).name for name in files})
    shown = ", ".join(names[:4])
    if len(names) > 4:
        shown += f", and {len(names) - 4} more"
    lean = [name for name in names if name.endswith(".lean")]
    kind = "no Lean source among them" if not lean else f"{len(lean)} of them Lean source"
    return (f"{project} has changed since the verification at {commit[:12]} "
            f"({shown}; {kind}); the receipt attests to that commit, not to what is there now")


def recorded_fingerprints() -> dict[str, str]:
    """The statement fingerprints as committed, without asking Lean.

    `compute_fingerprints` needs a built library, which is why receipt health used to be
    unavailable to the generated views. It does not have to be: `fingerprints.json` is committed
    and CI runs `fingerprint --check` against a real build, so a stale file fails there rather
    than quietly mis-colouring a box here.

    Deliberately not cached. The files are small and a view reads them a few dozen times, which
    costs nothing measurable; a cache would have to be invalidated when `_set_root` moves
    underneath it or when one is rewritten mid-run, and getting that wrong means colouring a box
    from a fingerprint that is no longer there.

    Reads the per-node files, and the retired root file as well if a working tree still has one,
    so that an older checkout reports what it reported then.
    """
    merged: dict[str, str] = {}
    paths = [FINGERPRINTS] if FINGERPRINTS.is_file() else []
    if NODES_DIR.is_dir():
        paths += sorted(NODES_DIR.glob(f"*/*/{FINGERPRINTS_NAME}"))
    for path in paths:
        merged.update(_fingerprint_entries(path))
    return merged


def _fingerprint_entries(path: pathlib.Path) -> dict[str, str]:
    """String digests from one fingerprint file.

    A file that is not a JSON object, or that stores a non-string digest, used to raise out of
    `status` and `pages` -- or, for a number, to crash later on `digest[:16]`. Dropping those
    entries makes `fingerprint --check` report the conclusion as unrecorded, which is the failure
    the check already has a name for.
    """
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        return {}
    if not isinstance(data, dict):
        return {}
    return {
        key: value
        for key, value in data.items()
        if isinstance(key, str) and isinstance(value, str)
    }


def receipt_state(conclusion_key: str, conclusion: dict) -> tuple[str, str] | None:
    """How the receipt behind a `lean-comparator` conclusion is standing right now.

    `None` when the conclusion does not designate `lean-comparator`, so there is no receipt for
    the question to be about. Otherwise `assess`'s verdict and its reason.
    """
    if designated_kind(conclusion) != "lean-comparator":
        return None
    receipt = load_receipt(conclusion_key)
    if receipt is None:
        return "BROKEN", "designated `lean-comparator` but no receipt file"
    # Views are generated and diffed by CI, so they must not depend on git history.
    return assess(conclusion_key, receipt, recorded_fingerprints(), consult_history=False)


#: `assess`'s verdict, as the views draw it. Environment staleness keeps the verification: the
#: proof still connects the same statements, and re-running it is bookkeeping. Statement drift
#: does not -- the implication that was checked no longer reaches what the node now claims, and
#: nothing short of a fresh Comparator run brings it back. Yellow and orange share a shade here
#: because what separates them -- whether the toolchain gap is wide enough to have fallen out of
#: the Mathlib cache -- is about how long re-running takes, not about what the receipt is worth.
#: `status` keeps the distinction.
_RECEIPT_DISPLAY = {
    "green": "lean-comparator",
    "yellow": "lean-comparator-stale",
    "orange": "lean-comparator-stale",
    "churn": "lean-comparator-stale",
    "BROKEN": "lean-comparator-drifted",
}


def display_kind(conclusion_key: str, conclusion: dict) -> str:
    """The evidence kind a reader of the views is actually being offered.

    `designated_kind` says what was *claimed*; this says what still *holds*. They differ exactly
    when a receipt has gone stale or been voided, and a view showing the first would go on
    reporting `verified` after the verified implication had been severed -- which is the one
    thing these files exist to make visible.
    """
    state = receipt_state(conclusion_key, conclusion)
    if state is None:
        return designated_kind(conclusion) or "none-yet"
    return _RECEIPT_DISPLAY.get(state[0], "lean-comparator-drifted")


def status() -> bool:
    """The traffic light for every conclusion."""
    nodes = load_nodes()
    fingerprints = compute_fingerprints()
    lights = {"green": 0, "yellow": 0, "orange": 0, "churn": 0, "BROKEN": 0, "-": 0}

    print("Conclusion status")
    print("=" * 78)
    for node_id, node in sorted(nodes.items()):
        for conclusion in conclusions_of(node):
            key = f"{node_id}.{conclusion.get('id')}"
            kind = designated_kind(conclusion)
            if kind == NONCOMPLIANT_KIND:
                # Saying "not Lean-verified" of this one would be false: the kernel accepted it.
                # What it has not got, and will not get while the obstruction stands, is a receipt
                # from this network.
                lights["-"] += 1
                print(f"  -       {key}")
                print("          a Lean proof this network has not certified; see its `note`")
                continue
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
    if lights["churn"]:
        print("\n`churn` is a fingerprint that moved while the Lean source did not -- the mark of")
        print("an environment bump rather than an edited theorem, since the digest is taken of the")
        print("ELABORATED statement and a renamed instance is enough to move it. Re-verify and")
        print("re-fingerprint; do NOT read it as someone having rewritten a statement. It is not")
        print("green either: a changed definition upstream could in principle change what the")
        print("statement means, and only a fresh run settles that.")
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
            used_ids = {j.get("id") for j in justifications}
            identifier = "comparator"
            suffix = 2
            while identifier in used_ids:
                identifier = f"comparator-{suffix}"
                suffix += 1
            existing = {
                "id": identifier,
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
        health = receipt_state(key, conclusion)
        if health is not None and health[0] == "BROKEN":
            kind = "lean-comparator-drifted"
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
        try:
            finished = subprocess.run(
                ["gh", "issue", "view", str(number), "--json", "state", "--jq", ".state"],
                cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
            )
        except OSError:
            continue
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
        if designated_kind(conclusion) in {"none-yet", "literature", "asserted",
                                           NONCOMPLIANT_KIND}
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
            # `traced` is deliberately not queued. Some of its missing edges are waiting on a
            # node that could exist, and some are algorithms or data that never can; nothing here
            # can tell those apart, and a queue full of items nobody can action is the failure
            # mode this file has already been through once.
            if import_status(conclusion) == "undetermined":
                tasks.append(
                    f"imports   {node_id}.{conclusion.get('id')}  (not yet traced to its sources)")
            if kind == "none-yet":
                tasks.append(f"justify   {node_id}.{conclusion.get('id')}  [{claim}]")
            elif kind in {"literature", "asserted"}:
                tasks.append(f"formalize {node_id}.{conclusion.get('id')}  ({kind}) [{claim}]")
            elif kind == NONCOMPLIANT_KIND:
                tasks.append(f"certify   {node_id}.{conclusion.get('id')}  "
                             f"(Lean proof, no receipt available) [{claim}]")

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

    Derivable without Lean, so that it stays cheap enough to regenerate in any pull request.
    That includes receipt health: `recorded_fingerprints` reads the committed `fingerprints.json`
    rather than rebuilding, and `assess` reads the committed manifest, so the Evidence column can
    say what a receipt is presently worth. What still needs Lean, and stays in `ieantn.py status`,
    is checking that `fingerprints.json` is itself current.

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
        "Derived from node metadata and the committed fingerprints, with no Lean. The Evidence",
        "column says what a receipt is presently worth, not merely what was claimed for it; the",
        "reason a receipt has stopped standing is below, and `python scripts/ieantn.py status`",
        "adds the environment detail.",
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
            key = f"{node_id}.{conclusion.get('id')}"
            lines.append(
                f"| `{node_id}` | {status} | `{conclusion.get('id')}` | "
                f"{display_kind(key, conclusion)} | {len(conclusion.get('imports') or [])} | "
                + (f"#{issue} |" if issue else "- |")
            )

    # A receipt that has stopped attesting to the current statement is the one thing here that
    # calls for action rather than description, so it gets said outright rather than left to be
    # inferred from a column. It is also what makes this file's diff useful in review: a pull
    # request that voids four receipts adds four lines below.
    ailing = [(key, state) for key, (_, conclusion) in sorted(index.items())
              if (state := receipt_state(key, conclusion)) and state[0] != "green"]
    if ailing:
        lines += [
            "",
            "## Receipts needing attention",
            "",
            "Conclusions designated `lean-comparator` whose receipt no longer stands clean.",
            "**Drifted** is not staleness: the verified implication no longer reaches what the",
            "node now claims, and only a fresh verification restores it.",
            "",
            "| Conclusion | State | Why |",
            "|---|---|---|",
        ]
        lines += [
            f"| `{key}` | {'drifted' if light == 'BROKEN' else light} | {detail} |"
            for key, (light, detail) in ailing
        ]

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
    lines += inactive_section()
    return "\n".join(lines) + "\n"


def inactive_section() -> list[str]:
    """The inactive nodes, listed so a retired directory is never a mystery.

    They are out of every other table by design; this is the one place they appear.
    """
    inactive = inactive_nodes()
    if not inactive:
        return []
    lines = [
        "",
        "## Inactive nodes",
        "",
        "Retired without a successor: out of the build and the graph, kept on disk. "
        "`python scripts/ieantn.py reactivate <node>` restores one.",
        "",
        "| Node | Why |",
        "|---|---|",
    ]
    for node_id, node in sorted(inactive.items()):
        reason = " ".join(str((node.get("node") or {}).get("inactive_reason") or "").split())
        lines.append(f"| `{node_id}` | {reason.replace('|', '/')} |")
    return lines


def state(check_only: bool, advisory: bool = False) -> bool:
    """Refresh `STATE.md`, or check it.

    `advisory` is what `check` passes: a stale view is reported and does not fail the run. See
    `DERIVED_NOTE`.
    """
    rendered = render_state(load_nodes())
    if check_only:
        problems = Problems()
        if (STATE.read_text(encoding="utf-8") if STATE.is_file() else "") != rendered:
            note = DERIVED_NOTE.format(command="state")
            (problems.warn if advisory else problems.add)(rel(STATE), note)
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
    "lean-comparator-stale": ("verified, stale", "#2da44e", "#e9f7ec"),
    "lean-comparator-drifted": ("verified, drifted", "#8b949e", "#eef2ef"),
    "lean-noncompliant": ("lean, noncompliant", "#4f5661", "#eaeef2"),
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
        if not any(stripped.startswith(prefix) for prefix in _DECLARATION_START):
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


#: The page's stylesheet. Inline, and no web fonts: the file has to work opened
#: from a clone with no network, which is most of why nothing is loaded from a CDN.
GRAPH_PAGE_CSS = """\
:root { color-scheme: light; --ink: #1f2328; --quiet: #57606a; --line: #d0d7de;
  --bg: #ffffff; --panel: #f6f8fa; }
* { box-sizing: border-box; }
body { margin: 0; padding: 0 20px 56px; background: var(--bg); color: var(--ink);
  font: 15px/1.55 -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif; }
header, nav, .controls, main, footer { max-width: 1180px; margin: 0 auto; }
header { padding: 28px 0 8px; }
h1 { font-size: 26px; margin: 0 0 6px; letter-spacing: -0.01em; }
header p { margin: 4px 0; color: var(--quiet); font-size: 13px; }
a { color: #0969da; }
code { font: 12px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  background: var(--panel); padding: 2px 5px; border-radius: 5px; }
.tabs { display: flex; gap: 6px; margin: 18px 0 0; border-bottom: 1px solid var(--line); }
.tabs button { appearance: none; border: 1px solid transparent; border-bottom: none;
  background: none; font: inherit; font-weight: 600; color: var(--quiet);
  padding: 9px 15px; border-radius: 8px 8px 0 0; cursor: pointer; margin-bottom: -1px; }
.tabs button.on { color: var(--ink); background: var(--bg);
  border-color: var(--line); }
.controls { display: flex; flex-wrap: wrap; gap: 14px 22px; align-items: center;
  padding: 14px 0 6px; font-size: 13px; }
.find input { font: inherit; padding: 6px 10px; border: 1px solid var(--line);
  border-radius: 7px; min-width: 15rem; }
fieldset { border: none; margin: 0; padding: 0; display: flex; flex-wrap: wrap;
  gap: 4px 14px; align-items: center; }
legend { float: left; margin-right: 12px; color: var(--quiet); padding: 0; }
.swatch { display: inline-flex; align-items: center; gap: 6px; cursor: pointer;
  white-space: nowrap; }
.swatch::after { content: ""; width: 11px; height: 11px; border-radius: 3px;
  background: var(--fill); border: 1.5px solid var(--stroke); }
.zoom button { font: inherit; min-width: 2em; padding: 4px 8px; cursor: pointer;
  border: 1px solid var(--line); border-radius: 6px; background: var(--bg); }
h2 { font-size: 19px; margin: 24px 0 4px; }
h3 { font-size: 15px; margin: 26px 0 4px; }
.count { color: var(--quiet); font-weight: 400; }
.blurb { margin: 0 0 12px; color: var(--quiet); font-size: 13px; max-width: 62em; }
.scroll { overflow: auto; border: 1px solid var(--line); border-radius: 10px;
  background: var(--panel); padding: 8px; max-height: 78vh; }
.drawing { display: block; }
.drawing text { font: 600 12px/1 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  text-anchor: middle; fill: var(--ink); pointer-events: none; }
.drawing text.bottom { font-weight: 400; font-size: 11px; fill: var(--quiet); }
.drawing a { text-decoration: none; }
.box, .edge { transition: opacity .12s ease-out; }
.box.dim { opacity: .13; }
.edge.dim { opacity: .07; }
.box:hover rect, .box:hover polygon { filter: brightness(.96); }
ul.alone { list-style: none; display: flex; flex-wrap: wrap; gap: 6px;
  margin: 0; padding: 0; }
ul.alone li { border: 1.5px var(--edge, solid) var(--stroke); background: var(--fill);
  border-radius: 7px; padding: 4px 9px; }
ul.alone a { color: var(--ink); text-decoration: none;
  font: 12px/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
ul.alone a:hover { text-decoration: underline; }
.note { color: var(--quiet); font-size: 13px; }
footer { margin-top: 34px; padding-top: 18px; border-top: 1px solid var(--line);
  color: var(--quiet); font-size: 13px; }
footer h2 { font-size: 15px; color: var(--ink); margin-top: 18px; }
footer dl { display: grid; grid-template-columns: max-content 1fr; gap: 4px 14px;
  margin: 8px 0 0; }
footer dt { font-weight: 600; color: var(--ink); }
footer dd { margin: 0; }
"""


#: Search, evidence filter, tab switch, zoom. ES5 and no libraries, for the same
#: reason. The drawing is static SVG underneath, so none of this is load-bearing:
#: with scripting off the picture is still there and still correct.
GRAPH_PAGE_SCRIPT = """\
(function () {
  var boxes = Array.prototype.slice.call(document.querySelectorAll('.box'));
  var edges = Array.prototype.slice.call(document.querySelectorAll('.edge'));
  var find = document.getElementById('find');
  var toggles = Array.prototype.slice.call(
    document.querySelectorAll('[data-kind-toggle]'));

  function apply() {
    var needle = find.value.trim().toLowerCase();
    var hidden = {};
    toggles.forEach(function (box) {
      if (!box.checked) { hidden[box.getAttribute('data-kind-toggle')] = true; }
    });
    var shown = {};
    boxes.forEach(function (box) {
      var key = box.getAttribute('data-key');
      var off = hidden[box.getAttribute('data-kind')] === true ||
        (needle !== '' && key.toLowerCase().indexOf(needle) === -1);
      box.classList.toggle('dim', off);
      if (!off) { shown[key] = true; }
    });
    // An edge is only as visible as the boxes it joins, or it would point at nothing.
    edges.forEach(function (edge) {
      edge.classList.toggle('dim', !(shown[edge.getAttribute('data-from')] &&
        shown[edge.getAttribute('data-to')]));
    });
  }

  find.addEventListener('input', apply);
  toggles.forEach(function (box) { box.addEventListener('change', apply); });

  Array.prototype.forEach.call(document.querySelectorAll('[data-tab]'),
    function (button) {
      button.addEventListener('click', function () {
        var want = button.getAttribute('data-tab');
        Array.prototype.forEach.call(document.querySelectorAll('[data-tab]'),
          function (other) {
            var on = other === button;
            other.classList.toggle('on', on);
            other.setAttribute('aria-selected', on ? 'true' : 'false');
          });
        Array.prototype.forEach.call(document.querySelectorAll('.panel'),
          function (panel) { panel.hidden = panel.id !== 'panel-' + want; });
      });
    });

  var scale = 1;
  function zoom(factor) {
    scale = factor === 'reset' ? 1 :
      Math.min(2.5, Math.max(0.25, scale * parseFloat(factor)));
    Array.prototype.forEach.call(document.querySelectorAll('.drawing'),
      function (svg) {
        var width = parseFloat(svg.getAttribute('data-width'));
        svg.setAttribute('width', Math.round(width * scale));
        svg.removeAttribute('height');
      });
  }
  Array.prototype.forEach.call(document.querySelectorAll('[data-zoom]'),
    function (button) {
      button.addEventListener('click', function () {
        zoom(button.getAttribute('data-zoom'));
      });
    });
}());
"""


#: The legend, which is the condensed form of what GRAPH.md says at length.
GRAPH_PAGE_LEGEND = """\
  <h2>How to read it</h2>
  <p>The colour of a box is the kind of evidence behind the step from its assumptions to its
  claim, and only green was checked by Lean here. Everything else is a leaf of the trust
  graph &mdash; something the network takes on faith, however reasonably &mdash; and the point of
  drawing it is that you can see exactly which.</p>
  <dl>
    <dt>Solid green</dt><dd>A verification receipt that still stands.</dd>
    <dt>Pale green</dt><dd><em>Stale</em>: only the environment has moved on, so re-running is
      bookkeeping.</dd>
    <dt>Grey-green</dt><dd><em>Drifted</em>: the statement itself changed since verification, so
      the checked implication no longer reaches what the node claims. Ranked below a bare
      assertion for that reason.</dd>
    <dt>Dashed border</dt><dd>The inputs are known and written down, but at least one is not the
      sort of thing an arrow can carry &mdash; an algorithm, a data set, a paper nobody has made
      a node of yet.</dd>
    <dt>Dotted border</dt><dd>Nobody has yet worked out what the claim assumes.</dd>
    <dt>Hexagon</dt><dd>A bridge: the step itself, proved in Lean and recompiled on every push.
      Drawn as a box rather than an arrow because a bridge may have several premises at once,
      which an arrow cannot say.</dd>
  </dl>
  <p>Every box links to its node's page, which carries the Lean spelling of the claim, its
  docstring, and everything recorded about why it should be believed.</p>
"""


#: The dash patterns of `imports_status`, as CSS border styles: the list of boxes that stand
#: alone has no arrows to carry the distinction, so its borders are all that is left to say it.
BORDER_STYLE = {"2 3": "dotted", "8 4": "dashed", "": "solid"}

#: What a hexagon is called in the evidence filter, where it sits beside the evidence kinds
#: without being one: a bridge is a step, not a grade of belief.
BRIDGE_LABEL = "bridge (a proved step)"


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
#: A drifted receipt sits second from the bottom on purpose. It is worth less *now* than a bare
#: assertion -- an assertion is at least a claim someone stands behind, where a voided receipt
#: supports nothing about the statement as it currently reads -- even though the node it belongs
#: to is usually one Comparator run away from being green again.
#: `lean-noncompliant` sits above the two kinds a reader can only take on authority: the proof is
#: here, the Lean kernel accepted it, and anyone may build it. It stays below `bridged` because a
#: bridge terminates in something this network checked, and nothing has checked this.
EVIDENCE_ORDER = ["none-yet", "lean-comparator-drifted", "asserted", "literature", "numerical",
                  "lean-noncompliant", "bridged", "lean-comparator-stale", "lean-comparator"]


def weakest_kind(node_id: str, conclusions: list[dict]) -> str:
    """The least-supported evidence kind among these conclusions."""
    kinds = [display_kind(f"{node_id}.{c.get('id')}", c) for c in conclusions]
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
        url = node_page_url(node_id, "" if key else cid, absolute=True)
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
            kind = weakest_kind(node_id, cs)
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
            lines.append(f"  style N{mermaid_id(node_id)} stroke-dasharray: 2 3;")
        elif cs and any(import_status(c) == "traced" for c in cs):
            lines.append(f"  style N{mermaid_id(node_id)} stroke-dasharray: 8 4;")
    for kind in EVIDENCE_ORDER:
        members = [f"N{mermaid_id(n)}" for n in sorted(nodes)
                   if (weakest_kind(n, conclusions_of(nodes[n]))
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
    # Escape underscores too: replacing every separator with `_` merged valid
    # keys such as A.v1.v1_main and A_v1.v1.main into a single diagram node.
    return re.sub(r"[^0-9A-Za-z]", lambda match: f"_{ord(match[0]):x}_", key)


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
        "Green comes in three shades, because a verification can stop being current in two quite",
        "different ways. **Solid green** is a receipt that still stands: the statement is byte for",
        "byte the one Comparator saw, in the environment it saw it in. **Pale green** — *stale* —",
        "means only the environment has moved on; the proof still connects exactly the same two",
        "statements, and re-running it is bookkeeping. **Faded grey-green** — *drifted* — means the",
        "statement itself has changed since verification, so the checked implication no longer",
        "reaches what the node now claims. That is not a weaker verification but an absent one, and",
        "it is ranked below an assertion accordingly: nothing short of a fresh Comparator run",
        "brings it back. `python scripts/ieantn.py status` says which claim moved.",
        "",
        "The diagram here carries the colours. The border and the hexagon described next are on",
        "the drawn page, which has the room for them.",
        "",
        "The border says how completely the arrows into a box tell the story, and the more broken",
        "it is the less they say. **Solid**: they tell all of it. **Dashed**: the inputs are known",
        "and written down, but at least one is not the sort of thing an arrow can carry — an",
        "algorithm, a data set, or a paper nobody has made a node of yet. This is the usual state",
        "of a claim resting on a computation. **Finely dotted**: nobody has yet worked out what the",
        "claim assumes, which is an admission that the question has not been asked rather than a",
        "claim that it rests on nothing.",
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
        "At full resolution the graph is **drawn** rather than written: see",
        f"[docs/graph.html]({REPOSITORY_URL}/blob/main/docs/graph.html), which carries this graph",
        "per conclusion and the one above per node version, with a search box, a filter by kind of",
        "evidence, and a link from every box to the page for its node.",
        "",
        "It is a file rather than a block here because this one outgrew what Markdown can show.",
        "GitHub renders Mermaid through a sandboxed viewer that refuses a diagram over 50,000",
        "characters, and the conclusion-level graph reached 63,621 -- so what a reader got was an",
        "error where the picture should have been. The drawn page has no such ceiling, and the",
        "layout is computed when the file is generated, so it is as reproducible as the Markdown",
        "was: `python scripts/ieantn.py graph` writes both, and CI diffs both.",
        "",
        "Open it from a clone, or enable GitHub Pages for `docs/` to have it at a URL. The two",
        "tables below say the same thing in text, and need nothing but this file.",
        "",
    ]

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
        kind = display_kind(key, conclusion)
        label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
        mark = "  " * depth
        repeated = " *(above)*" if key in seen else ""
        pending = {"undetermined": " — *sources not traced*",
                   "traced": " — *sources known, not all drawable*"}.get(
                       import_status(conclusion), "")
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
            kind = display_kind(key, index[key][1])
            label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
            traced = {"undetermined": "**not yet traced**",
                      "traced": "known, not all drawable",
                      "none": "none",
                      "identified": "traced"}.get(import_status(index[key][1]), "traced")
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


def node_page_url(node_id: str, anchor: str = "", from_root: bool = False,
                  absolute: bool = False) -> str:
    """A link to a node's page.

    Three forms, and all three are needed.

    `from_root` because GRAPH.md sits at the repository root while the node pages link to each
    other from inside `docs/nodes/`; a path right for one is broken for the other.

    `absolute` because GitHub renders Mermaid in a sandboxed iframe served from
    `viewscreen.githubusercontent.com`, so a relative `click` href resolves against *that* origin
    and 404s — `https://viewscreen.githubusercontent.com/markdown/docs/nodes/Lcm-v1.md` is what a
    reader actually got. Ordinary Markdown links on the same page are fine, because they are
    rendered in the repository's own context; only the diagram is sandboxed. This is invisible
    locally and invisible in CI: it can only be caught by clicking a box on GitHub.
    """
    fragment = f"#{anchor}" if anchor else ""
    if absolute:
        return f"{REPOSITORY_URL}/blob/main/docs/nodes/{node_id.replace('.', '-')}.md{fragment}"
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
        # The evidence a reader would actually want to open. Naming the path without linking it
        # made them reconstruct the URL by hand, which is the sort of friction that stops people
        # checking at all.
        # `Solution.lean`, not `is_dir()`. A solution directory keeps its `.lake` build tree,
        # which is git-ignored and therefore SURVIVES A BRANCH SWITCH that removes every tracked
        # file under it. The directory then still exists, holding nothing but build artefacts, and
        # `is_dir()` reported a solution that the branch does not have -- a page that regenerates
        # differently depending on which branch you last built. Marker files, not directories.
        solution = SOLUTIONS / node_id
        if (solution / "Solution.lean").is_file():
            out.append(f"| Solution | [`Solutions/{node_id}`]"
                       f"({REPOSITORY_URL}/tree/main/Solutions/{node_id}) |")
        receipt = RECEIPTS / f"{key}.json"
        if receipt.is_file():
            out.append(f"| Receipt | [`{receipt.name}`]"
                       f"({REPOSITORY_URL}/blob/main/receipts/{receipt.name}) |")
        kind = designated_kind(conclusion) or "none-yet"
        shown = display_kind(key, conclusion)
        label, _, _ = EVIDENCE_STYLE.get(shown, (shown, "", ""))
        out.append(f"| Evidence | {label} (`{kind}`) |")
        # `drifted` on its own invites the reader to assume the worst -- a wrong proof rather than
        # a moved statement -- so the page says which statement moved and leaves them to judge.
        health = receipt_state(key, conclusion)
        if health and health[0] != "green":
            out.append(f"| Receipt state | {health[1]} |")
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
        kind = weakest_kind(node_id, cs) if cs else "none-yet"
        label, _, _ = EVIDENCE_STYLE.get(kind, (kind, "", ""))
        out.append(f"| [`{node_id}`]({node_id.replace('.', '-')}.md) "
                   f"| {_quote((node.get('node') or {}).get('kind'))} | {len(cs)} "
                   f"| {label if cs else '—'} |")
    out += inactive_section()
    out.append("")
    return "\n".join(out) + "\n"


def pages(check_only: bool, advisory: bool = False) -> bool:
    """Write (or verify) one page per node. `advisory` as in `state`."""
    nodes = load_nodes()
    index = index_conclusions(nodes)
    importers = importers_of(nodes)
    wanted = {node_page_path(node_id): render_node_page(node_id, nodes, index, importers)
              for node_id in sorted(nodes)}
    wanted[PAGES / "README.md"] = render_pages_index(nodes, index)

    if check_only:
        problems = Problems()
        report = problems.warn if advisory else problems.add
        for path, text in sorted(wanted.items()):
            current = path.read_text(encoding="utf-8") if path.is_file() else ""
            if current != text:
                report(rel(path), DERIVED_NOTE.format(command="pages"))
        for path in sorted(PAGES.glob("*.md")) if PAGES.is_dir() else []:
            if path not in wanted:
                report(rel(path), "no such node any more; `pages` deletes it")
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


# ---------------------------------------------------------------------------
# The drawn graph: docs/graph.html
# ---------------------------------------------------------------------------

#: Geometry of a drawing, in SVG user units. A box holds `Family.v1` over a conclusion id at
#: 12px, and that is what sets the column pitch.
BOX_WIDTH, BOX_HEIGHT = 208, 46
COLUMN_GAP, ROW_GAP, MARGIN = 76, 16, 28

#: Barycentre sweeps. Four is where the crossing count stops improving on a graph this shape,
#: and a fixed number is what keeps the output reproducible.
LAYOUT_SWEEPS = 4


def layered_layout(vertices: list[str], edges: list[tuple[str, str]],
                   rank: dict[str, tuple]) -> dict[str, tuple[int, int]]:
    """Place a DAG in columns: `(layer, slot)` for every vertex.

    Layer by longest path, so an arrow always points rightwards and its reach says how much of
    the network stands behind the claim at its head. Slots within a column are then ordered by
    the mean slot of each vertex's neighbours -- the barycentre heuristic, swept down and up --
    which is the cheap standard way to pull connected boxes level and take out crossings.

    **Deterministic**, which is the requirement that chose this over laying out in the browser:
    a view this repository commits has to be diffable, so every tie breaks on `rank`, the sweep
    count is fixed, and nothing consults a set's iteration order.
    """
    predecessors: dict[str, list[str]] = {vertex: [] for vertex in vertices}
    successors: dict[str, list[str]] = {vertex: [] for vertex in vertices}
    for source, target in edges:
        if source in predecessors and target in predecessors:
            successors[source].append(target)
            predecessors[target].append(source)

    layer: dict[str, int] = {}

    def depth(vertex: str, stack: frozenset) -> int:
        if vertex in layer:
            return layer[vertex]
        # `check_graph` rejects an import cycle, so this cannot happen in a network that passes
        # the checks. Guard anyway: a drawing command is not where anyone wants to meet one.
        if vertex in stack:
            return 0
        found = 0
        for source in predecessors[vertex]:
            found = max(found, 1 + depth(source, stack | {vertex}))
        layer[vertex] = found
        return found

    ordered = sorted(vertices, key=lambda vertex: rank[vertex])
    for vertex in ordered:
        depth(vertex, frozenset())

    columns: dict[int, list[str]] = {}
    for vertex in ordered:
        columns.setdefault(layer[vertex], []).append(vertex)
    slot = {vertex: index for column in columns.values()
            for index, vertex in enumerate(column)}

    for sweep in range(LAYOUT_SWEEPS):
        downward = sweep % 2 == 0
        neighbours = predecessors if downward else successors
        for index in sorted(columns, reverse=not downward):
            def centre(vertex: str) -> float:
                near = [slot[other] for other in neighbours[vertex] if other in slot]
                return sum(near) / len(near) if near else float(slot[vertex])
            columns[index].sort(key=lambda vertex: (centre(vertex), rank[vertex]))
            for position, vertex in enumerate(columns[index]):
                slot[vertex] = position

    return {vertex: (layer[vertex], slot[vertex]) for vertex in vertices}


def html_escape(value) -> str:
    """Text safe in element content and in a double-quoted attribute."""
    return (str(value).replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;").replace('"', "&quot;"))


#: How much prose a tooltip gets. Enough for the statement and the sentence that qualifies it;
#: a docstring runs to 1,950 characters at the longest, and a tooltip is not where to read that.
SUMMARY_BUDGET = 420


def summary_text(text: str, budget: int = SUMMARY_BUDGET) -> str:
    """A docstring or description, folded into a few lines a tooltip can show.

    Whole paragraphs, because the first one is usually a fragment: a conclusion docstring tends
    to open with a bolded name and run the statement itself onto the next paragraph, so cutting
    at the first blank line would show `**Chebyshev's upper bound.** For every x >= 30,` and stop
    there. Paragraphs are taken until the budget is spent, and an ellipsis admits what was left.

    Wrapped here rather than left to the tooltip, which does not reliably wrap, and stripped of
    the `**` that marks bold in prose nobody is rendering. Backticks stay: they are what tells a
    reader that `psi` is the Lean name rather than the letter.
    """
    paragraphs = [" ".join(block.split())
                  for block in (text or "").strip().split("\n\n") if block.strip()]
    kept: list[str] = []
    spent = 0
    for paragraph in paragraphs:
        remaining = budget - spent
        if remaining < 60:
            kept.append("...")
            break
        if len(paragraph) > remaining:
            # Shorten the paragraph that crosses the line rather than dropping it. Dropping it
            # cost `KadiriLumley.v1.table_2` everything after its opening clause, because what it
            # had to say came after the first blank line and did not fit whole.
            kept.append(textwrap.shorten(paragraph, width=remaining, placeholder=" ..."))
            break
        kept.append(paragraph)
        spent += len(paragraph)
    folded = "\n\n".join(kept).replace("**", "")
    return "\n".join(textwrap.fill(block, width=78) if block != "..." else block
                      for block in folded.split("\n\n"))


def render_drawing(boxes: list[dict], edges: list[dict]) -> str:
    """One `<svg>`: the boxes placed, and the edges between them.

    Static. The search, the filters and the zoom on the page are enhancements over this, so the
    picture is still there with JavaScript off -- which is also what makes it renderable straight
    from a blob view or an offline clone.
    """
    placement = layered_layout(
        [box["key"] for box in boxes],
        [(edge["from"], edge["to"]) for edge in edges],
        {box["key"]: box["rank"] for box in boxes},
    )
    at = {}
    for box in boxes:
        layer, slot = placement[box["key"]]
        at[box["key"]] = (MARGIN + layer * (BOX_WIDTH + COLUMN_GAP),
                          MARGIN + slot * (BOX_HEIGHT + ROW_GAP))
    width = max((x for x, _ in at.values()), default=0) + BOX_WIDTH + MARGIN
    height = max((y for _, y in at.values()), default=0) + BOX_HEIGHT + MARGIN

    out = [
        f'<svg class="drawing" viewBox="0 0 {width} {height}" width="{width}" '
        f'height="{height}" data-width="{width}" xmlns="http://www.w3.org/2000/svg" '
        f'role="img" aria-label="The network as a layered graph">',
        '  <defs>',
        '    <marker id="arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7"',
        '        markerHeight="7" orient="auto-start-reverse">',
        '      <path d="M 0 0 L 8 4 L 0 8 z" fill="#57606a"/>',
        '    </marker>',
        '    <marker id="arrow-bridge" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6"',
        '        markerHeight="6" orient="auto-start-reverse">',
        f'      <path d="M 0 0 L 8 4 L 0 8 z" fill="{BRIDGE_STYLE[0]}"/>',
        '    </marker>',
        '  </defs>',
        '  <g class="edges" fill="none">',
    ]
    for edge in sorted(edges, key=lambda e: (e["from"], e["to"])):
        if edge["from"] not in at or edge["to"] not in at:
            continue
        x1, y1 = at[edge["from"]]
        x2, y2 = at[edge["to"]]
        start = (x1 + BOX_WIDTH, y1 + BOX_HEIGHT / 2)
        end = (x2, y2 + BOX_HEIGHT / 2)
        reach = max((end[0] - start[0]) * 0.45, 24)
        bridge = edge.get("bridge")
        out.append(
            f'    <path class="edge{" bridge" if bridge else ""}" '
            f'd="M {start[0]:.0f} {start[1]:.0f} C {start[0] + reach:.0f} {start[1]:.0f}, '
            f'{end[0] - reach:.0f} {end[1]:.0f}, {end[0]:.0f} {end[1]:.0f}" '
            f'stroke="{BRIDGE_STYLE[0] if bridge else "#57606a"}" '
            f'stroke-width="{2.4 if bridge else 1.2}" '
            f'marker-end="url(#{"arrow-bridge" if bridge else "arrow"})" '
            f'data-from="{html_escape(edge["from"])}" data-to="{html_escape(edge["to"])}"/>')
    out.append('  </g>')

    for box in sorted(boxes, key=lambda b: b["rank"]):
        x, y = at[box["key"]]
        dash = f' stroke-dasharray="{box["dash"]}"' if box.get("dash") else ""
        shape = (
            f'<polygon points="{x + 14},{y} {x + BOX_WIDTH - 14},{y} '
            f'{x + BOX_WIDTH},{y + BOX_HEIGHT / 2:.0f} {x + BOX_WIDTH - 14},{y + BOX_HEIGHT} '
            f'{x + 14},{y + BOX_HEIGHT} {x},{y + BOX_HEIGHT / 2:.0f}" '
            f'fill="{box["fill"]}" stroke="{box["stroke"]}" stroke-width="1.5"{dash}/>'
            if box.get("shape") == "hexagon" else
            f'<rect x="{x}" y="{y}" width="{BOX_WIDTH}" height="{BOX_HEIGHT}" rx="7" '
            f'fill="{box["fill"]}" stroke="{box["stroke"]}" stroke-width="1.5"{dash}/>')
        out += [
            f'  <g class="box" data-key="{html_escape(box["key"])}" '
            f'data-kind="{html_escape(box["kind"])}">',
            f'    <title>{html_escape(box["title"])}</title>',
            f'    <a href="{html_escape(box["href"])}" target="_blank" rel="noopener">',
            f'      {shape}',
            f'      <text x="{x + BOX_WIDTH / 2:.0f}" y="{y + 19}" class="top">'
            f'{html_escape(box["top"])}</text>',
            f'      <text x="{x + BOX_WIDTH / 2:.0f}" y="{y + 34}" class="bottom">'
            f'{html_escape(box["bottom"])}</text>',
            '    </a>',
            '  </g>',
        ]
    out.append('</svg>')
    return "\n".join(out)


def graph_boxes(nodes: dict, index: dict, level: str) -> tuple[list[dict], list[dict]]:
    """The boxes and edges of one drawing: `claims` per conclusion, `nodes` per node version."""
    boxes: list[dict] = []
    edges: list[dict] = []
    if level == "claims":
        for key in sorted(index):
            node_id, conclusion = index[key]
            kind = display_kind(key, conclusion)
            label, stroke, fill = EVIDENCE_STYLE.get(kind, (kind, "#57606a", "#f6f8fa"))
            status = import_status(conclusion)
            boxes.append({
                "key": key, "rank": (node_id, key), "kind": kind,
                "top": node_id, "bottom": key.rsplit(".", 1)[1],
                "fill": fill, "stroke": stroke,
                "dash": {"undetermined": "2 3", "traced": "8 4"}.get(status, ""),
                "href": node_page_url(node_id, anchor=key.rsplit(".", 1)[1], absolute=True),
                # The claim's own docstring, not the node's description: at this resolution a box
                # is one conclusion, and the node's paragraph would say the same thing over every
                # box of the node while describing none of them.
                "title": f"{key}\nevidence: {label}\nimports: {status}\n\n"
                         + summary_text(read_declaration(node_id, key.rsplit(".", 1)[1])[0]),
            })
            for dependency in conclusion.get("imports") or []:
                source = f"{dependency.get('node')}.{dependency.get('conclusion')}"
                if source in index:
                    edges.append({"from": source, "to": key})
        for bridge in bridges_in(nodes):
            if bridge["conclusion"] not in index:
                continue
            stem = pathlib.PurePosixPath(bridge["file"]).stem or bridge["id"]
            boxes.append({
                "key": bridge["id"], "rank": ("~bridge", bridge["id"]), "kind": "bridge",
                "top": stem, "bottom": "bridge" if bridge["designated"] else "bridge (spare)",
                "fill": BRIDGE_STYLE[1], "stroke": BRIDGE_STYLE[0], "dash": "",
                "shape": "hexagon",
                "href": f"{REPOSITORY_URL}/blob/main/{bridge['file']}",
                "title": f"{bridge['file']}\nproves: {bridge['conclusion']}\n"
                         f"from: {', '.join(bridge['premises'])}",
            })
            for premise in bridge["premises"]:
                if premise in index:
                    edges.append({"from": premise, "to": bridge["id"], "bridge": True})
            edges.append({"from": bridge["id"], "to": bridge["conclusion"], "bridge": True})
    else:
        for node_id in sorted(nodes):
            conclusions = conclusions_of(nodes[node_id])
            kind = weakest_kind(node_id, conclusions) if conclusions else "none-yet"
            label, stroke, fill = EVIDENCE_STYLE.get(kind, (kind, "#57606a", "#f6f8fa"))
            count = len(conclusions)
            boxes.append({
                "key": node_id, "rank": (node_id,), "kind": kind,
                "top": node_id,
                "bottom": f"{count} claim{'' if count == 1 else 's'} · {label}",
                "fill": fill, "stroke": stroke, "dash": "",
                "href": node_page_url(node_id, absolute=True),
                "title": f"{node_id}\nweakest evidence: {label}\n{count} conclusion(s)\n\n"
                         + summary_text((nodes[node_id].get("project") or {})
                                        .get("description") or ""),
            })
        seen = set()
        for key in sorted(index):
            node_id, conclusion = index[key]
            for dependency in conclusion.get("imports") or []:
                source = f"{dependency.get('node')}.{dependency.get('conclusion')}"
                if source in index:
                    pair = (index[source][0], node_id)
                    if pair[0] != pair[1] and pair not in seen:
                        seen.add(pair)
                        edges.append({"from": pair[0], "to": pair[1]})
    return boxes, edges


def render_graph_page(nodes: dict[str, dict]) -> str:
    """`docs/graph.html`: both graphs, drawn, with the boxes that stand alone listed beside them.

    Two things the Mermaid blocks could not do. It holds a network this size -- the conclusion
    graph had outgrown what GitHub will render -- and it separates the claims that take part in
    the dependency structure from the ones that do not. Forty-one of the conclusions have no edge
    at all in either direction; drawing them among the rest cost most of the width and told a
    reader nothing, so they are a list under the picture instead.
    """
    index = index_conclusions(nodes)
    # Once per level, not once per use: filling the tooltips reads every `Conclusions.lean`.
    drawings = {level: graph_boxes(nodes, index, level) for level in ("claims", "nodes")}
    panels = []
    for level, heading, blurb in (
        ("claims", "Every claim",
         "One box per conclusion, grouped left to right by what it rests on. A thin arrow "
         "means the box at its head <em>assumes</em> the box at its tail; a thick arrow runs "
         "through a hexagon, which is a bridge proved in Lean."),
        ("nodes", "Node versions",
         "The same thing with each node version as one box, summarised by its weakest "
         "conclusion. Edges between conclusions of the same node version are not drawn."),
    ):
        boxes, edges = drawings[level]
        linked = {edge["from"] for edge in edges} | {edge["to"] for edge in edges}
        drawn = [box for box in boxes if box["key"] in linked]
        alone = [box for box in boxes if box["key"] not in linked]
        panel = [
            f'<section class="panel" id="panel-{level}"'
            f'{"" if level == "claims" else " hidden"}>',
            f'  <h2>{heading}</h2>',
            f'  <p class="blurb">{blurb}</p>',
            f'  <div class="scroll">{render_drawing(drawn, edges) if drawn else ""}</div>',
        ]
        if alone:
            panel += [
                f'  <h3>Stands alone <span class="count">{len(alone)}</span></h3>',
                '  <p class="blurb">Nothing in the network imports these, and they import '
                'nothing. That is not a defect -- an unconditional theorem has nothing to '
                'assume -- but it is why they are not in the picture.</p>',
                '  <ul class="alone">',
            ]
            for box in sorted(alone, key=lambda b: b["rank"]):
                panel.append(
                    f'    <li class="box" data-key="{html_escape(box["key"])}" '
                    f'data-kind="{html_escape(box["kind"])}" '
                    f'style="--fill:{box["fill"]};--stroke:{box["stroke"]};'
                    f'--edge:{BORDER_STYLE.get(box.get("dash", ""), "solid")}">'
                    f'<a href="{html_escape(box["href"])}" target="_blank" rel="noopener" '
                    f'title="{html_escape(box["title"])}">'
                    f'{html_escape(box["key"])}</a></li>')
            panel.append('  </ul>')
        panel.append('</section>')
        panels += panel

    kinds = sorted({box["kind"] for boxes, _ in drawings.values() for box in boxes})
    toggles = []
    for kind in kinds:
        label = (BRIDGE_LABEL if kind == "bridge"
                 else EVIDENCE_STYLE.get(kind, (kind, "", ""))[0])
        _, stroke, fill = (BRIDGE_STYLE[0], BRIDGE_STYLE[0], BRIDGE_STYLE[1]) \
            if kind == "bridge" else EVIDENCE_STYLE.get(kind, (kind, "#57606a", "#f6f8fa"))
        toggles.append(
            f'      <label class="swatch" style="--fill:{fill};--stroke:{stroke}">'
            f'<input type="checkbox" checked data-kind-toggle="{html_escape(kind)}">'
            f'{html_escape(label)}</label>')

    return "\n".join([
        "<!doctype html>",
        '<html lang="en">',
        "<head>",
        '<meta charset="utf-8">',
        '<meta name="viewport" content="width=device-width, initial-scale=1">',
        "<title>IEANTN · the network</title>",
        f"<style>{GRAPH_PAGE_CSS}</style>",
        "</head>",
        "<body>",
        "<header>",
        "  <h1>The network</h1>",
        "  <p><strong>Generated file &mdash; do not edit.</strong> Regenerated by "
        "<code>python scripts/ieantn.py graph</code>.</p>",
        f'  <p class="links"><a href="{REPOSITORY_URL}/blob/main/GRAPH.md">GRAPH.md</a> for the '
        f'same content as prose and tables · <a href="{REPOSITORY_URL}/blob/main/STATE.md">'
        f'STATE.md</a> · <a href="nodes/README.md">the node pages</a> · '
        f'<a href="{REPOSITORY_URL}/blob/main/docs/ARCHITECTURE.md">ARCHITECTURE.md</a></p>',
        "</header>",
        '<nav class="tabs" role="tablist">',
        '  <button data-tab="claims" class="on" aria-selected="true">Every claim</button>',
        '  <button data-tab="nodes" aria-selected="false">Node versions</button>',
        "</nav>",
        '<form class="controls" onsubmit="return false">',
        '  <label class="find">Find <input type="search" id="find" '
        'placeholder="Buthe, psi, FKS2.v1 ..." autocomplete="off"></label>',
        '  <fieldset><legend>Evidence</legend>',
        *toggles,
        "  </fieldset>",
        '  <span class="zoom">Zoom <button data-zoom="0.8" type="button">&minus;</button>'
        '<button data-zoom="1.25" type="button">+</button>'
        '<button data-zoom="reset" type="button">reset</button></span>',
        "</form>",
        '<noscript><p class="note">The pictures below are plain SVG and need no JavaScript; '
        "only the search, the evidence filter and the zoom do.</p></noscript>",
        "<main>",
        *panels,
        "</main>",
        f"<footer>{GRAPH_PAGE_LEGEND}</footer>",
        f"<script>{GRAPH_PAGE_SCRIPT}</script>",
        "</body>",
        "</html>",
        "",
    ])


def graph(check_only: bool, advisory: bool = False) -> bool:
    """Refresh `GRAPH.md` and `docs/graph.html`, or check them. `advisory` as in `state`.

    Two files from one command, because they are two renderings of one thing and a reader who
    found them disagreeing would have no way to tell which was stale.
    """
    nodes = load_nodes()
    wanted = {GRAPH: render_graph(nodes), GRAPH_PAGE: render_graph_page(nodes)}
    if check_only:
        problems = Problems()
        for path, rendered in wanted.items():
            if (path.read_text(encoding="utf-8") if path.is_file() else "") != rendered:
                note = DERIVED_NOTE.format(command="graph")
                (problems.warn if advisory else problems.add)(rel(path), note)
        return problems.report("network graph")
    for path, rendered in wanted.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered, encoding="utf-8", newline="\n")
        print(f"wrote {rel(path)}")
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
        fingerprints = recorded_fingerprints()
        receipts = {
            path.stem: json.loads(path.read_text(encoding="utf-8"))
            for path in (RECEIPTS.glob("*.json") if RECEIPTS.is_dir() else [])
        }
    else:
        listed = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ref],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        )
        if listed.returncode != 0:
            sys.exit(f"error: cannot read network base `{ref}`: " + listed.stderr.strip())
        listing = listed.stdout.splitlines()
        nodes = {}
        for path in listing:
            if path.startswith("IEANTN/Nodes/") and path.endswith("formalization.yaml"):
                raw = git_show(ref, path)
                if raw is None:
                    sys.exit(f"error: cannot read `{path}` at network base `{ref}`")
                data = yaml.safe_load(raw) or {}
                if is_inactive(data):
                    continue
                directory = ROOT / pathlib.PurePosixPath(path).parent
                data["_dir"] = directory
                nodes[node_id_of(directory)] = data
        # Both layouts: per-node files now, one root file at any commit before the split.
        fingerprints = {}
        for path in listing:
            if path == "fingerprints.json" or (
                path.startswith("IEANTN/Nodes/") and path.endswith(f"/{FINGERPRINTS_NAME}")
            ):
                raw = git_show(ref, path)
                if raw:
                    fingerprints.update(json.loads(raw))
        receipts = {}
        for path in listing:
            if path.startswith("receipts/") and path.endswith(".json"):
                raw = git_show(ref, path)
                if raw:
                    receipts[pathlib.PurePosixPath(path).stem] = json.loads(raw)

    conclusions = {}
    for node_id, node in nodes.items():
        for conclusion in conclusions_of(node):
            designated = designated_of(conclusion) or {}
            conclusions[f"{node_id}.{conclusion.get('id')}"] = {
                "imports": [
                    f"{d.get('node')}.{d.get('conclusion')}"
                    for d in (conclusion.get("imports") or [])
                ],
                "kind": designated.get("kind"),
                "from": bridge_sources(designated) if designated.get("kind") == "bridged" else [],
            }
    return {"conclusions": conclusions, "fingerprints": fingerprints, "receipts": receipts}


def graph_leaves(conclusions: dict, key: str, seen: set[str] | None = None) -> list[str]:
    """The unproved-in-Lean conclusions `key` rests on, from a `state_at` snapshot.

    A `bridged` conclusion contributes nothing of its own: what it rests on is whatever its
    sources rest on. A `lean-comparator` conclusion is proved in this network. Anything else is a
    leaf, and imports are walked in every case. Receipt health is not consulted. A severed
    receipt is a different event, and `diff` already reports it. This is only the shape of the
    graph, which is why it needs no Lean run.
    """
    seen = set() if seen is None else seen
    if key in seen or key not in conclusions:
        return []
    seen.add(key)
    entry = conclusions[key]
    found: list[str] = []
    if entry.get("kind") == "bridged":
        for source in entry.get("from") or []:
            found += graph_leaves(conclusions, source, seen)
    elif entry.get("kind") not in VERIFIED_KINDS:
        found.append(key)
    for dependency in entry.get("imports") or []:
        found += graph_leaves(conclusions, dependency, seen)
    return found


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
            # Only importers that survive the change can break. One leaving in the same change --
            # a node deactivated together with its only consumer -- is not a dangling edge.
            users = [u for u in importers_before.get(key, []) if u in after["conclusions"]]
            if users:
                errors.append(
                    f"**`{key}` was removed** but {len(users)} conclusion(s) still import it at "
                    f"the base: {', '.join(f'`{u}`' for u in users)}."
                )
            elif key.rsplit(".", 1)[0] in inactive_nodes():
                notes.append(f"`{key}` deactivated (its node is now inactive); nothing imported it.")
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
                if name in excused:
                    # A receipt breaking is the CONSEQUENCE of the restatement acknowledged above,
                    # not a second event. Reporting both made an acknowledgement that covered the
                    # cause still fail the branch, which reads as the mechanism not working.
                    continue
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

    # A bridge is a restatement. It may discharge assumptions; it may not acquire any. Comparing
    # the leaf set before and after is the whole check, and it is a property of the graph, so a
    # conclusion that did not exist at the base has nothing to compare against.
    for key, entry in sorted(after["conclusions"].items()):
        if entry.get("kind") != "bridged" or key not in before["conclusions"]:
            continue
        before_leaves = set(graph_leaves(before["conclusions"], key))
        after_leaves = set(graph_leaves(after["conclusions"], key))
        added = sorted(after_leaves - before_leaves)
        removed = sorted(before_leaves - after_leaves)
        if added:
            gained = ", ".join(f"`{name}`" for name in added)
            message = f"**`{key}` gained unproved assumptions** via its bridge: {gained}."
            if removed:
                lost = ", ".join(f"`{name}`" for name in removed)
                message += f" It no longer rests on {lost}."
            message += (
                " A restatement must not rest on more than it did. Discharge the new "
                "assumptions, or do not designate the bridge: designate the weaker evidence "
                "the node actually has, which costs nothing and says the true thing. This is "
                "the one `diff` error a `changes/*.yaml` acknowledgement does not cover -- see "
                "docs/ROADMAP.md."
            )
            errors.append(message)
        elif removed:
            lost = ", ".join(f"`{name}`" for name in removed)
            notes.append(
                f"`{key}` rests on fewer unproved assumptions after its bridge: {lost}."
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
    elif (
        justification.get("kind") not in VERIFIED_KINDS
        or (receipt_state(key, conclusion) or (None, ""))[0] == "BROKEN"
    ):
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


def _ident_boundary(code: str, index: int, word: str) -> bool:
    if not code.startswith(word, index):
        return False
    if index and (code[index - 1].isalnum() or code[index - 1] in "_'"):
        return False
    after = index + len(word)
    return after >= len(code) or not (code[after].isalnum() or code[after] in "_'")


def _skip_ws(code: str, index: int) -> int:
    while index < len(code) and code[index].isspace():
        index += 1
    return index


def _read_lean_name(code: str, index: int) -> tuple[str, int]:
    if index >= len(code) or not (code[index].isalpha() or code[index] == "_"):
        return "", index
    end = index + 1
    while end < len(code) and (code[end].isalnum() or code[end] in "_'."):
        end += 1
    return code[index:end], end


def _skip_string(code: str, index: int) -> int:
    index += 1
    while index < len(code):
        if code[index] == "\\":
            index += 2
            continue
        if code[index] == '"':
            return index + 1
        index += 1
    return len(code)


def _balanced_group(code: str, index: int) -> tuple[str, int]:
    closing = {"(": ")", "[": "]", "{": "}"}
    start = index
    stack = [closing[code[index]]]
    index += 1
    while index < len(code) and stack:
        if code[index] == '"':
            index = _skip_string(code, index)
            continue
        if code[index] in closing:
            stack.append(closing[code[index]])
        elif code[index] == stack[-1]:
            stack.pop()
        index += 1
    return code[start:index], index


def _split_top_colon(text: str) -> tuple[str, str] | None:
    closing = {"(": ")", "[": "]", "{": "}"}
    stack: list[str] = []
    index = 0
    while index < len(text):
        if text[index] == '"':
            index = _skip_string(text, index)
            continue
        if text[index] in closing:
            stack.append(closing[text[index]])
        elif stack and text[index] == stack[-1]:
            stack.pop()
        elif text[index] == ":" and not stack:
            return text[:index], text[index + 1:]
        index += 1
    return None


def _until_assign(code: str, index: int) -> tuple[str, int]:
    closing = {"(": ")", "[": "]", "{": "}"}
    stack: list[str] = []
    start = index
    while index < len(code):
        if code.startswith(":=", index) and not stack:
            return code[start:index], index
        if code[index] == '"':
            index = _skip_string(code, index)
            continue
        if code[index] in closing:
            stack.append(closing[code[index]])
        elif stack and code[index] == stack[-1]:
            stack.pop()
        index += 1
    return code[start:], len(code)


def bridge_theorems(text: str, target: str, known: set[str]) -> list[tuple[str, list[str]]]:
    """Theorems whose conclusion is exactly `target` and whose hypotheses are known declarations.

    A dotted name at the top level is used as written. A short name is prefixed with the
    namespaces open around it. A dotted name inside a namespace is skipped: which full name Lean
    would assign is not something to guess. Only a single explicit `(name : type)` binder is
    accepted, and only when `type` is one of `known`. An implicit binder or a side condition
    disqualifies that theorem.
    """
    code = strip_lean_comments(text)
    stack: list[str] = []
    found: list[tuple[str, list[str]]] = []
    index, length = 0, len(code)
    while index < length:
        if _ident_boundary(code, index, "namespace"):
            index = _skip_ws(code, index + len("namespace"))
            name, index = _read_lean_name(code, index)
            stack.extend(part for part in name.split(".") if part)
            continue
        if _ident_boundary(code, index, "end"):
            index = _skip_ws(code, index + len("end"))
            name, next_index = _read_lean_name(code, index)
            if name:
                parts = [part for part in name.split(".") if part]
                if len(stack) >= len(parts) and stack[-len(parts):] == parts:
                    del stack[-len(parts):]
                elif stack:
                    stack.pop()
                index = next_index
            elif stack:
                stack.pop()
            else:
                index += 1
            continue
        if not _ident_boundary(code, index, "theorem"):
            index += 1
            continue
        index = _skip_ws(code, index + len("theorem"))
        declared, index = _read_lean_name(code, index)
        ambiguous = "." in declared and bool(stack)
        if "." in declared or not stack:
            full_name = declared
        else:
            full_name = ".".join([*stack, declared])
        index = _skip_ws(code, index)
        binders: list[str] = []
        usable = bool(declared) and not ambiguous
        while index < length and code[index] in "({[":
            if code[index] != "(":
                usable = False
                break
            group, index = _balanced_group(code, index)
            split = _split_top_colon(group[1:-1])
            if split is None:
                usable = False
                break
            binder_name, binder_type = split
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", binder_name.strip()):
                usable = False
                break
            binders.append(" ".join(binder_type.split()))
            index = _skip_ws(code, index)
        if index < length and code[index] == ":":
            conclusion, index = _until_assign(code, index + 1)
        else:
            conclusion, index = _until_assign(code, index)
            usable = False
        conclusion = " ".join(conclusion.split())
        if (
            usable
            and conclusion == target
            and all(binder in known for binder in binders)
        ):
            found.append((full_name, binders))
        if code.startswith(":=", index):
            index += 2
    return found


def import_keys_of(conclusion: dict) -> list[str]:
    return [
        f"{dependency.get('node')}.{dependency.get('conclusion')}"
        for dependency in (conclusion.get("imports") or [])
    ]


def hypothesis_of(key: str) -> str:
    node_id, conclusion_id = key.rsplit(".", 1)
    return hypothesis_name({"node": node_id, "conclusion": conclusion_id})


def rewrite_vendored_imports(text: str, stems: dict[str, str]) -> str:
    """Repoint imports of a solution's own files at the directory they were copied into.

    Positions come from the comment-stripped text, which keeps the same length, so the
    replacement lands on the import the reader wrote and not on one mentioned in a comment.
    """
    stripped = strip_lean_comments(text)
    pieces: list[str] = []
    cursor = 0
    for match in IMPORT_RE.finditer(stripped):
        module = match.group(1)
        head, dot, tail = module.partition(".")
        if head not in stems:
            continue
        start, end = match.span(1)
        pieces.append(text[cursor:start])
        pieces.append(stems[head] + (dot + tail if dot else ""))
        cursor = end
    if not pieces:
        return text
    pieces.append(text[cursor:])
    return "".join(pieces)


def vendored_module(node_id: str, stem: str) -> str:
    return f"vendored.{node_id}.{stem}"


def vendor_solution(node_id: str, target: pathlib.Path) -> None:
    """Copy one node's solution under `vendored/<Family>/<version>/`.

    `Solution.lean` becomes `NodeSolution.lean` so the wrapper can keep the name `Solution`.
    Imports of sibling files are rewritten to that directory; an import that should have moved
    and did not is a failure, not a successful copy of a file that no longer resolves.
    """
    solution_dir = SOLUTIONS / node_id
    destination = target.joinpath("vendored", *node_id.split("."))
    destination.mkdir(parents=True, exist_ok=True)
    files = sorted(path for path in solution_dir.glob("*.lean"))
    stems = {
        path.stem: vendored_module(node_id, "NodeSolution" if path.name == "Solution.lean" else path.stem)
        for path in files
    }
    for path in files:
        original = path.read_text(encoding="utf-8")
        local = [
            module for module in IMPORT_RE.findall(strip_lean_comments(original))
            if module.split(".", 1)[0] in stems
        ]
        rewritten = rewrite_vendored_imports(original, stems)
        if local and rewritten == original:
            sys.exit(
                f"error: {rel(path)} imports `{local[0]}`, and copying it under vendored/ "
                "did not rewrite that import."
            )
        name = "NodeSolution.lean" if path.name == "Solution.lean" else path.name
        (destination / name).write_text(rewritten, encoding="utf-8", newline="\n")


def plan_composition(index: dict, key: str) -> tuple[dict | None, str | None]:
    """How to prove `key` from its unjustified leaves, or why that cannot be emitted.

    A `lean-comparator` step is its solution's challenge theorem, applied to its imports.
    A `bridged` step is the one theorem in the bridge file whose conclusion is that
    declaration and whose hypotheses are themselves conclusions. Anything else is a
    hypothesis only when it imports nothing. A citation that still depends on something
    is a gap: assuming it would drop those dependencies, and there is no proof to compose.
    """
    if key not in index:
        return None, (
            f"error: unknown conclusion `{key}`; try `python scripts/ieantn.py report`"
        )
    node_id, conclusion = index[key]
    kind = (designated_of(conclusion) or {}).get("kind")
    if kind not in VERIFIED_KINDS and kind != "bridged":
        return None, (
            f"error: `{key}` designates `{kind}`, so there is no Lean proof to "
            "submit. Palomar records a verified formalization, not a claim."
        )

    declarations: dict[str, list[str]] = {}
    for conclusion_key, (_, item) in index.items():
        declaration = item.get("declaration")
        if isinstance(declaration, str):
            declarations.setdefault(declaration, []).append(conclusion_key)
    known = set(declarations)

    leaves: list[str] = []
    vendors: list[str] = []
    bridge_modules: list[str] = []
    bridge_calls: dict[str, tuple[str, list[str]]] = {}
    visiting: set[str] = set()
    visited: set[str] = set()

    def walk(current: str) -> str | None:
        if current in visited:
            return None
        if current in visiting:
            return f"error: `{current}` sits on a cycle, so there is no order to compose it in."
        if current not in index:
            return f"error: `{current}` is not a conclusion in this network."
        visiting.add(current)
        current_node, current_conclusion = index[current]
        justification = designated_of(current_conclusion) or {}
        current_kind = justification.get("kind")
        dependencies = import_keys_of(current_conclusion)
        if current_kind in VERIFIED_KINDS:
            health = receipt_state(current, current_conclusion)
            if health is not None and health[0] == "BROKEN":
                return f"error: `{current}` has no standing verification receipt: {health[1]}"
            if not (SOLUTIONS / current_node / "Solution.lean").is_file():
                return f"error: no solution at {rel(SOLUTIONS / current_node)}"
            vendors.append(current_node)
            for dependency in dependencies:
                error = walk(dependency)
                if error:
                    return error
        elif current_kind == "bridged":
            relative = justification.get("bridge")
            if not isinstance(relative, str):
                return f"error: `{current}` names no bridge file that exists."
            bridge_path = ROOT / relative
            if not bridge_path.is_file():
                return f"error: `{current}` names no bridge file that exists."
            target_decl = current_conclusion.get("declaration")
            if not isinstance(target_decl, str):
                return f"error: `{current}` has no declaration to match a bridge theorem against."
            matches = bridge_theorems(bridge_path.read_text(encoding="utf-8"), target_decl, known)
            if len(matches) != 1:
                return (
                    f"error: `{relative}` has {len(matches)} theorems whose conclusion is "
                    f"`{target_decl}` and whose hypotheses are conclusions of this network. "
                    "Refusing to guess an application."
                )
            full_name, binder_types = matches[0]
            binder_keys: list[str] = []
            for binder_type in binder_types:
                owners = declarations.get(binder_type, [])
                if len(owners) != 1:
                    return (
                        f"error: `{relative}` hypothesis `{binder_type}` names "
                        f"{len(owners)} conclusions. Refusing to guess which."
                    )
                binder_keys.append(owners[0])
            bridge_calls[current] = (full_name, binder_keys)
            module = relative[:-5] if relative.endswith(".lean") else relative
            bridge_modules.append(module.replace("/", "."))
            for source in [*bridge_sources(justification), *dependencies, *binder_keys]:
                error = walk(source)
                if error:
                    return error
        elif dependencies:
            listed = ", ".join(f"`{item}`" for item in dependencies)
            return (
                f"error: `{current}` is `{current_kind}` and still imports {listed}. "
                "That is a gap in the proof, not a hypothesis: a citation in the middle "
                "has nothing to compose, and assuming it would drop what it depends on."
            )
        else:
            leaves.append(current)
        visiting.remove(current)
        visited.add(current)
        return None

    error = walk(key)
    if error:
        return None, error

    ordered = sorted(set(leaves))
    one_level = kind in VERIFIED_KINDS and set(import_keys_of(conclusion)) == set(ordered)

    def apply(name: str, arguments: list[str]) -> str:
        if not arguments:
            return name
        return f"({name} {' '.join(arguments)})"

    if one_level:
        # The single application is written the way it always was: the theorem, then the
        # hypotheses in sorted order, with no extra parentheses. A reader diffing a one-level
        # submission against the previous generator should see the same proof line.
        arguments = " ".join(hypothesis_of(leaf) for leaf in ordered)
        term = f"{node_id}.challenge_{conclusion.get('id')}"
        if arguments:
            term += " " + arguments
    else:
        def term_for(current: str) -> str:
            if current in set(ordered):
                return hypothesis_of(current)
            current_node, current_conclusion = index[current]
            current_kind = (designated_of(current_conclusion) or {}).get("kind")
            if current_kind in VERIFIED_KINDS:
                return apply(
                    f"{current_node}.challenge_{current_conclusion.get('id')}",
                    [term_for(item) for item in import_keys_of(current_conclusion)],
                )
            full_name, binder_keys = bridge_calls[current]
            return apply(full_name, [term_for(item) for item in binder_keys])

        term = term_for(key)

    return {
        "leaves": ordered,
        "term": term,
        "vendors": sorted(set(vendors)),
        "bridge_modules": sorted(set(bridge_modules)),
        "one_level": one_level,
        "node_id": node_id,
        "conclusion": conclusion,
    }, None



def spinoff(key: str, out: str, compile_check: bool) -> bool:
    """Emit one conclusion as a self-contained Palomar submission.

    See docs/ARCHITECTURE.md section 7. The Challenge inlines every IEANTN definition the statement
    needs, so its import closure is Mathlib-only as Palomar requires. The Solution is the one-level
    case when every hypothesis is a direct import, and otherwise the composition of the designated
    path: each verified node's challenge theorem applied to the steps above it, and each bridge
    applied to the conclusions its theorem actually takes.
    """
    nodes = load_nodes()
    index = index_conclusions(nodes)
    plan, error = plan_composition(index, key)
    if error or plan is None:
        print(error)
        return False
    node_id = plan["node_id"]
    conclusion = plan["conclusion"]
    cid = conclusion.get("id")
    leaves = plan["leaves"]

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
            if current is not None and current[1]:
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
    if current and current[1]:
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
    proof = f"""
theorem {SPINOFF_NAMESPACE}.main{binders} :
    {statement} :=
  {plan["term"]}
"""
    if plan["one_level"]:
        solution_dir = SOLUTIONS / node_id
        vendored = sorted("NodeSolution" if path.stem == "Solution" else path.stem
                          for path in solution_dir.glob("*.lean"))
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
"""
            + proof)
        (target / "Solution.lean").write_text(solution, encoding="utf-8", newline="\n")
        for path in solution_dir.glob("*.lean"):
            if path.name != "Solution.lean":
                (target / path.name).write_text(path.read_text(encoding="utf-8"),
                                                encoding="utf-8", newline="\n")
        vendor = solution_dir / "Solution.lean"
        (target / "NodeSolution.lean").write_text(vendor.read_text(encoding="utf-8"),
                                                  encoding="utf-8", newline="\n")
    else:
        for vendor_id in plan["vendors"]:
            vendor_solution(vendor_id, target)
        imported = [vendored_module(vendor_id, "NodeSolution") for vendor_id in plan["vendors"]]
        imported += plan["bridge_modules"]
        solution = (
            LICENCE_HEADER
            + "".join(f"import {module}\n" for module in imported)
            + f"""
/-!
# Solution: `{key}`

**Generated file** -- regenerated by `python scripts/ieantn.py spinoff {key}`.

The proof composes the designated path. Each verified node contributes its challenge theorem,
vendored under `vendored/`. A bridge contributes the theorem in the core library whose conclusion
is that node's declaration. The names stay the ones Comparator compared, so this file only applies
them.
-/
"""
            + proof)
        (target / "Solution.lean").write_text(solution, encoding="utf-8", newline="\n")

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
    if leaves:
        print("     add a limitation naming each hypothesis:")
        for leaf in leaves:
            print(f"       - {leaf}")
    else:
        print("     there are no hypotheses to name in the limitations")
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
        text = re.sub(
            rf"(?<![\w']){re.escape(old_id)}(?![\w'])", new_id, text
        )
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
        # Solutions are not copied: the old hole count and path do not describe this version.
        conclusion.pop("progress", None)
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


def referenced_nodes(node: dict) -> set[str]:
    """Nodes which must remain live for this node's metadata to be well-formed."""
    references = {
        str(d.get("node"))
        for c in conclusions_of(node) for d in (c.get("imports") or [])
    }
    references.update(
        source.rsplit(".", 1)[0]
        for c in conclusions_of(node) for j in justifications_of(c)
        if j.get("kind") == "bridged" for source in bridge_sources(j)
    )
    replacement = (node.get("node") or {}).get("superseded_by")
    if replacement:
        references.add(replacement)
    return references


def _lean_import_blockers(paths: list[pathlib.Path], node_ids: set[str]) -> list[str]:
    """Lean consumers of the nodes, including edges not recorded in metadata."""
    prefixes = [f"IEANTN.Nodes.{node_id}" for node_id in node_ids]
    return sorted(
        f"{rel(path)} -> {module}"
        for path in paths for module in imports_of(path)
        if any(under(module, prefix) for prefix in prefixes)
    )


def deactivate(node_ids: list[str], reason: str) -> bool:
    """Take nodes out of the network without deleting them.

    For nodes that were built to support something more interesting and ended up unused. Refuses
    while anything live still imports one of them, since a deactivated node is out of the build and
    the importer would stop compiling; deactivating several at once is allowed so that a node and
    the one thing it served can go together.
    """
    # Process each node once so repeated CLI arguments cannot overwrite its saved status.
    node_ids = list(dict.fromkeys(node_ids))
    reason = " ".join(reason.split())
    if not reason:
        print("error: say why, with --reason; the reason is what lets someone reactivate it later")
        return False
    everything = load_nodes(include_inactive=True)
    unknown = [n for n in node_ids if n not in everything]
    if unknown:
        print(f"error: unknown node(s): {', '.join(unknown)}")
        return False
    already = [n for n in node_ids if is_inactive(everything[n])]
    if already:
        print(f"error: already inactive: {', '.join(already)}")
        return False

    going = set(node_ids)
    blockers = sorted(
        f"{node_id} -> {target}"
        for node_id, node in everything.items()
        if node_id not in going and not is_inactive(node)
        for target in referenced_nodes(node) & going
    )
    # A bridge whose target is going out with the node is not a live consumer of it: a node and
    # the bridge that justifies it are deactivated together or not at all.
    going_bridges = {
        (ROOT / justification["bridge"]).resolve()
        for node_id in going
        for conclusion in conclusions_of(everything[node_id])
        for justification in justifications_of(conclusion)
        if justification.get("kind") == "bridged" and justification.get("bridge")
    }
    live_files = [
        path for node_id, node in everything.items()
        if node_id not in going and not is_inactive(node)
        for path in node["_dir"].glob("*.lean")
    ] + [path for path in BRIDGES_DIR.rglob("*.lean")
         if path.resolve() not in going_bridges]
    blockers += _lean_import_blockers(live_files, going)
    if blockers:
        print("error: still imported or referenced by live nodes:")
        for line in blockers:
            print(f"  {line}")
        print("deactivate those too, or drop the edges first.")
        return False

    from ruamel.yaml.scalarstring import FoldedScalarString

    for node_id in node_ids:
        path = everything[node_id]["_dir"] / "formalization.yaml"
        writer, data = edit_yaml(path)
        meta = data["node"]
        # Insert right after `status`, and move whatever trailed it -- a comment, or the blank line
        # that separates the `node:` block from the next -- to the last key added, so the block
        # reads the same as a hand-written one.
        trailing = meta.ca.items.pop("status", None)
        at = list(meta).index("status") + 1
        meta.insert(at, "status_before_deactivation", meta.get("status"))
        meta.insert(at + 1, "inactive_reason", FoldedScalarString(reason))
        meta.insert(at + 2, "deactivated", datetime.date.today().isoformat())
        meta["status"] = INACTIVE
        if trailing is not None:
            meta.ca.items["deactivated"] = trailing
        with path.open("w", encoding="utf-8", newline="\n") as handle:
            writer.dump(data, handle)
        print(f"deactivated {node_id}")
    gen_challenges(check_only=False)
    print("\nits files are kept; it is out of the umbrella, so the core build no longer compiles it.")
    print("next: python scripts/ieantn.py fingerprint && python scripts/ieantn.py check")
    print("      (STATE, GRAPH and the node pages are rewritten on `main` by derived.yml)")
    return True


def reactivate(node_id: str) -> bool:
    """Undo `deactivate`: restore the status the node had, and put it back in the network."""
    everything = load_nodes(include_inactive=True)
    if node_id not in everything:
        print(f"error: unknown node `{node_id}`")
        return False
    if not is_inactive(everything[node_id]):
        print(f"error: `{node_id}` is not inactive")
        return False
    still_off = sorted(
        target for target in referenced_nodes(everything[node_id])
        if target != node_id and target in everything and is_inactive(everything[target])
    )
    if still_off:
        print(f"error: `{node_id}` references inactive {', '.join(still_off)}; reactivate those first")
        return False

    lean_blockers = _lean_import_blockers(
        list(everything[node_id]["_dir"].glob("*.lean")),
        {other for other, node in everything.items() if other != node_id and is_inactive(node)},
    )
    if lean_blockers:
        print("error: Lean files still import inactive nodes:")
        for line in lean_blockers:
            print(f"  {line}")
        return False

    path = everything[node_id]["_dir"] / "formalization.yaml"
    writer, data = edit_yaml(path)
    meta = data["node"]
    meta["status"] = meta.get("status_before_deactivation") or "active"
    trailing = meta.ca.items.pop("deactivated", None)
    for key in ("status_before_deactivation", "inactive_reason", "deactivated"):
        meta.pop(key, None)
    if trailing is not None:
        meta.ca.items["status"] = trailing
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        writer.dump(data, handle)
    print(f"reactivated {node_id} as `{data['node']['status']}`")
    gen_challenges(check_only=False)
    print("next: python scripts/ieantn.py fingerprint && python scripts/ieantn.py check")
    return True


# ---------------------------------------------------------------------------


def main() -> int:
    # A Windows console is cp1252 by default, and several of these reports carry em dashes and
    # Lean's turnstile. Without this the *reporting* crashes on characters the analysis handled
    # perfectly well -- `diff` did, on the text of a `changes/` acknowledgement -- which reads as
    # a tooling failure. The encoding is left alone so redirected output stays byte-faithful;
    # only the reaction to an unencodable character changes.
    for stream in (sys.stdout, sys.stderr):
        # `getattr` rather than a direct call: these are typed `TextIO`, which does not declare
        # `reconfigure` even though the concrete `TextIOWrapper` has it, and pyright rejects the
        # direct form. A redirected or wrapped stream may genuinely lack it.
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            try:
                reconfigure(errors="replace")
            except ValueError:  # detached, or already closed
                pass

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
    partial = sub.add_parser("progress")
    partial.add_argument("node", help="e.g. FKS2.v1")
    partial.add_argument("--write", action="store_true",
                         help="record the derived hole count in formalization.yaml")
    verification = sub.add_parser("verify")
    verification.add_argument("node", help="e.g. Lcm.v1")
    target = verification.add_mutually_exclusive_group(required=True)
    target.add_argument("--branch", help="branch to record the receipt on")
    target.add_argument("--pr", type=int, metavar="N",
                        help="verify pull request N; a fork's head is copied to a branch here "
                             "first, since the receipt job writes to this repository")
    verification.add_argument("--watch-only", action="store_true",
                              help="follow the latest run instead of dispatching a new one")
    verification.add_argument("--skip-precheck", action="store_true",
                              help="dispatch without first checking the solution is complete")
    snapshot = sub.add_parser("state")
    snapshot.add_argument("--check", action="store_true", help="fail instead of rewriting")
    fresh = sub.add_parser("new-node")
    fresh.add_argument("family", help="e.g. FKS2")
    fresh.add_argument(
        "--kind", default="paper", choices=["paper", "pipeline", "folklore", "computation", "standard"]
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
    shelve = sub.add_parser(
        "deactivate", help="retire nodes with no successor: out of the build and graph, kept on disk"
    )
    shelve.add_argument("nodes", nargs="+", help="e.g. CH2.v4 ContourIntegration.v1")
    shelve.add_argument("--reason", required=True, help="why; recorded in node.inactive_reason")
    unshelve = sub.add_parser("reactivate", help="undo deactivate")
    unshelve.add_argument("node", help="e.g. CH2.v4")

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
    if args.command == "progress":
        return 0 if progress(args.node, args.write) else 1
    if args.command == "verify":
        branch = args.branch
        if args.pr is not None:
            branch = branch_for_pr(args.pr)
            if branch is None:
                return 1
        return 0 if verify(args.node, branch, not args.watch_only,
                           precheck=not args.skip_precheck, pr=args.pr) else 1
    if args.command == "spinoff":
        return 0 if spinoff(args.conclusion, args.out, args.compile) else 1
    if args.command == "new-version":
        return 0 if new_version(args.family) else 1
    if args.command == "deprecate":
        return 0 if deprecate(args.node, args.replacement) else 1
    if args.command == "deactivate":
        return 0 if deactivate(args.nodes, args.reason) else 1
    if args.command == "reactivate":
        return 0 if reactivate(args.node) else 1
    if args.command == "check":
        # The last three are views, not sources: CI regenerates them on `main`, so `check`
        # reports a stale one and does not fail on it. See DERIVED_NOTE.
        return 0 if all(
            [check_closure(), check_graph(), check_pins(), check_receipts(online=False),
             gen_challenges(True), state(True, advisory=True), graph(True, advisory=True),
             pages(True, advisory=True)]
        ) else 1
    return 2


if __name__ == "__main__":
    sys.exit(main())
