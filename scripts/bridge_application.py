#!/usr/bin/env python3
"""Describe one narrow bridge theorem without treating the description as a proof.

The form is the one ``bridge_theorems`` already refuses to guess past: a full name,
explicit ``(name : type)`` premise binders, and a conclusion. A dotted declaration
written inside a namespace, an implicit binder, or two theorems that both match the
conclusion is an error. ``spinoff`` is left as it is.

    python3 scripts/bridge_application.py describe BRIDGE.lean --target A.v1.main --known B.v1.main
    python3 scripts/bridge_application.py check-equivalent

``check-equivalent`` extracts the namespace spelling and the full-name spelling of one
core-only theorem and, when ``lean`` is on ``PATH``, elaborates each spelling. A
toolchain failure skips that live check. Neither command claims the theorem is proved.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


class BridgeDescriptionError(Exception):
    """The source does not determine one narrow bridge application."""


@dataclass(frozen=True)
class ExplicitPremise:
    name: str
    binder_type: str


@dataclass(frozen=True)
class BridgeApplication:
    """A syntactic application. Holding one does not mean Lean has checked a proof."""

    full_name: str
    premises: tuple[ExplicitPremise, ...]
    conclusion: str


@dataclass(frozen=True)
class SpellingCheck:
    application: BridgeApplication
    lean: str
    detail: str


NAMESPACE_SPELLING = (
    "namespace Demo\n"
    "theorem from_b (h : True) : True := h\n"
    "end Demo\n"
)
FULL_NAME_SPELLING = "theorem Demo.from_b (h : True) : True := h\n"
EQUIVALENT_TARGET = "True"
EQUIVALENT_KNOWN = frozenset({EQUIVALENT_TARGET})

_OPENERS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
_IDENT_TAIL = set("_'.")


def strip_lean_comments(text: str) -> str:
    """Blank ``--`` and nested ``/- -/`` comments, keeping every other character position."""
    out: list[str] = []
    index, length = 0, len(text)
    while index < length:
        if text.startswith("--", index):
            while index < length and text[index] != "\n":
                out.append(" ")
                index += 1
            continue
        if text.startswith("/-", index):
            out.extend("  ")
            index += 2
            depth = 1
            while index < length and depth:
                if text.startswith("/-", index):
                    depth += 1
                    out.extend("  ")
                    index += 2
                    continue
                if text.startswith("-/", index):
                    depth -= 1
                    out.extend("  ")
                    index += 2
                    continue
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
            continue
        if text[index] == '"':
            out.append(" ")
            index += 1
            while index < length:
                if text[index] == "\\" and index + 1 < length:
                    nxt = text[index + 1]
                    out.append("\n" if nxt == "\n" else " ")
                    out.append(" ")
                    index += 2
                    continue
                if text[index] == '"':
                    out.append(" ")
                    index += 1
                    break
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
            continue
        out.append(text[index])
        index += 1
    return "".join(out)


def _collapse(text: str) -> str:
    return " ".join(text.split())


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
    while end < len(code) and (code[end].isalnum() or code[end] in _IDENT_TAIL):
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
    start = index
    stack = [_OPENERS[code[index]]]
    index += 1
    while index < len(code) and stack:
        if code[index] == '"':
            index = _skip_string(code, index)
            continue
        if code[index] in _OPENERS:
            stack.append(_OPENERS[code[index]])
        elif code[index] == stack[-1]:
            stack.pop()
        index += 1
    return code[start:index], index


def _split_top_colon(text: str) -> tuple[str, str] | None:
    stack: list[str] = []
    index = 0
    while index < len(text):
        if text[index] == '"':
            index = _skip_string(text, index)
            continue
        if text[index] in _OPENERS:
            stack.append(_OPENERS[text[index]])
        elif stack and text[index] == stack[-1]:
            stack.pop()
        elif text[index] == ":" and not stack:
            return text[:index], text[index + 1 :]
        index += 1
    return None


def _until_assign(code: str, index: int) -> tuple[str, int]:
    stack: list[str] = []
    start = index
    while index < len(code):
        if code.startswith(":=", index) and not stack:
            return code[start:index], index
        if code[index] == '"':
            index = _skip_string(code, index)
            continue
        if code[index] in _OPENERS:
            stack.append(_OPENERS[code[index]])
        elif stack and code[index] == stack[-1]:
            stack.pop()
        index += 1
    return code[start:], len(code)


@dataclass(frozen=True)
class _Theorem:
    declared: str
    full_name: str
    ambiguous: bool
    implicit: bool
    malformed: bool
    premises: tuple[ExplicitPremise, ...]
    conclusion: str


def _scan(text: str) -> list[_Theorem]:
    code = strip_lean_comments(text)
    stack: list[str] = []
    found: list[_Theorem] = []
    index, length = 0, len(code)
    while index < length:
        if _ident_boundary(code, index, "namespace"):
            index = _skip_ws(code, index + len("namespace"))
            name, next_index = _read_lean_name(code, index)
            if not name:
                index = max(next_index, index + 1)
                continue
            stack.extend(part for part in name.split(".") if part)
            index = next_index
            continue
        if _ident_boundary(code, index, "end"):
            index = _skip_ws(code, index + len("end"))
            name, next_index = _read_lean_name(code, index)
            if name:
                parts = [part for part in name.split(".") if part]
                if len(stack) >= len(parts) and stack[-len(parts) :] == parts:
                    del stack[-len(parts) :]
                elif stack:
                    stack.pop()
                index = next_index
            elif stack:
                stack.pop()
                index = max(next_index, index + 1)
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
        premises: list[ExplicitPremise] = []
        implicit = False
        malformed = not bool(declared)
        while index < length and code[index] in _OPENERS:
            opener = code[index]
            group, index = _balanced_group(code, index)
            if opener != "(":
                implicit = True
            else:
                split = _split_top_colon(group[1:-1]) if group.endswith(")") else None
                if split is None:
                    malformed = True
                else:
                    binder_name, binder_type = split
                    binder_name = binder_name.strip()
                    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", binder_name) is None:
                        malformed = True
                    else:
                        premises.append(ExplicitPremise(binder_name, _collapse(binder_type)))
            index = _skip_ws(code, index)
        if index < length and code[index] == ":":
            conclusion, index = _until_assign(code, index + 1)
        else:
            conclusion, index = _until_assign(code, index)
            malformed = True
        found.append(
            _Theorem(
                declared=declared,
                full_name=full_name,
                ambiguous=ambiguous,
                implicit=implicit,
                malformed=malformed,
                premises=tuple(premises),
                conclusion=_collapse(conclusion),
            )
        )
        if code.startswith(":=", index):
            index += 2
    return found


def describe_bridge(text: str, target: str, known: set[str] | frozenset[str] | None = None) -> BridgeApplication:
    """Return the one theorem whose conclusion is ``target``.

    ``known`` restricts premise types. ``None`` accepts every explicit premise type.
    """
    wanted = _collapse(target)
    known_norm = None if known is None else {_collapse(item) for item in known}
    clean: list[_Theorem] = []
    problems: list[str] = []
    skipped: list[str] = []
    for theorem in _scan(text):
        if theorem.conclusion != wanted:
            continue
        label = theorem.declared or theorem.full_name or "<unnamed>"
        if theorem.ambiguous:
            opened = "the open namespace" if not label else f"`{label}`"
            problems.append(
                f"ambiguous dotted name {opened} inside a namespace. "
                "Refusing to guess which full name Lean would assign."
            )
            continue
        if theorem.implicit:
            problems.append(
                f"theorem `{theorem.full_name}` has an implicit binder. "
                "The narrow form allows only explicit `(name : type)` premises."
            )
            continue
        if theorem.malformed:
            problems.append(
                f"theorem `{theorem.full_name or label}` does not use a single explicit "
                "`(name : type)` binder before its conclusion."
            )
            continue
        if known_norm is not None:
            unknown = [premise.binder_type for premise in theorem.premises if premise.binder_type not in known_norm]
            if unknown:
                skipped.append(
                    f"theorem `{theorem.full_name}` concludes `{wanted}` but premise "
                    f"`{unknown[0]}` is not a known declaration. Refusing to guess an application."
                )
                continue
        clean.append(theorem)
    if problems:
        raise BridgeDescriptionError(problems[0])
    if len(clean) > 1:
        names = " and ".join(f"`{theorem.full_name}`" for theorem in clean)
        raise BridgeDescriptionError(
            f"two theorems match conclusion `{wanted}`: {names}. Refusing to guess an application."
        )
    if len(clean) == 1:
        theorem = clean[0]
        return BridgeApplication(theorem.full_name, theorem.premises, theorem.conclusion)
    if skipped:
        raise BridgeDescriptionError(skipped[0])
    raise BridgeDescriptionError(
        f"no theorem matches conclusion `{wanted}` with explicit premise binders."
    )


def format_application(application: BridgeApplication) -> str:
    lines = [f"full_name: {application.full_name}", "premises:"]
    if application.premises:
        lines.extend(
            f"  - ({premise.name} : {premise.binder_type})" for premise in application.premises
        )
    else:
        lines.append("  - (none)")
    lines.append(f"conclusion: {application.conclusion}")
    lines.append("note: syntactic description only; this does not claim a proof")
    return "\n".join(lines) + "\n"


def equivalent_spelling_file() -> str:
    """One text containing both spellings. Lean elaborates each half on its own."""
    return (
        "-- Two equivalent spellings of one theorem: a namespace declaration and its full name.\n"
        "-- A single Lean environment cannot declare both, so each spelling is elaborated alone.\n"
        "-- No Mathlib import: both spellings use only core `True`.\n"
        "-- >>> spelling: namespace\n"
        f"{NAMESPACE_SPELLING}"
        "-- >>> spelling: full name\n"
        f"{FULL_NAME_SPELLING}"
    )


def _spelling_bodies(source: str) -> tuple[str, str]:
    namespace_mark = "-- >>> spelling: namespace\n"
    full_mark = "-- >>> spelling: full name\n"
    if namespace_mark not in source or full_mark not in source:
        raise BridgeDescriptionError("equivalent-spelling file is missing a spelling marker")
    after_namespace = source.split(namespace_mark, 1)[1]
    namespace_body, full_body = after_namespace.split(full_mark, 1)
    return namespace_body, full_body


def _toolchain_failure(text: str) -> bool:
    lowered = text.lower()
    markers = ("toolchain", "elan", "download", "install lean", "could not find a lean")
    return any(marker in lowered for marker in markers)


def _elaborate(body: str) -> subprocess.CompletedProcess[str] | None:
    """Elaborate ``body`` with core Lean only. ``None`` means ``lean`` is not on ``PATH``."""
    lean = shutil.which("lean")
    if lean is None:
        return None
    header = (
        "set_option autoImplicit false\n"
        "set_option relaxedAutoImplicit false\n"
        "-- self-contained: no Mathlib import\n\n"
    )
    with tempfile.TemporaryDirectory(prefix="bridge-application-") as directory:
        path = Path(directory) / "BridgeSpelling.lean"
        path.write_text(header + body, encoding="utf-8", newline="\n")
        try:
            return subprocess.run(
                [lean, str(path)],
                cwd=directory,
                capture_output=True,
                text=True,
                encoding="utf-8",
                timeout=60,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return subprocess.CompletedProcess([lean, str(path)], 124, "", "lean timed out")


def check_equivalent_spellings(source: str | None = None) -> SpellingCheck:
    """Extract both spellings and elaborate each when ``lean`` can run.

    The returned application is identical for the two spellings, or this raises.
    ``lean`` is ``"checked"`` when both self-contained files elaborate, and
    ``"skipped"`` when ``lean`` is absent or fails because of the toolchain.
    """
    combined = equivalent_spelling_file() if source is None else source
    if "import Mathlib" in combined:
        raise BridgeDescriptionError("the equivalent-spelling file must not import Mathlib")
    namespace_body, full_body = _spelling_bodies(combined)
    namespace_app = describe_bridge(namespace_body, EQUIVALENT_TARGET, set(EQUIVALENT_KNOWN))
    full_app = describe_bridge(full_body, EQUIVALENT_TARGET, set(EQUIVALENT_KNOWN))
    if namespace_app != full_app:
        raise BridgeDescriptionError(
            "namespace and full-name spellings extracted different applications: "
            f"{namespace_app} vs {full_app}"
        )
    results = [_elaborate(namespace_body), _elaborate(full_body)]
    if any(result is None for result in results):
        return SpellingCheck(namespace_app, "skipped", "lean is not on PATH")
    failures = [result for result in results if result is not None and result.returncode != 0]
    if not failures:
        return SpellingCheck(namespace_app, "checked", "both spellings elaborated")
    output = "\n".join((result.stdout or "") + (result.stderr or "") for result in failures)
    if all(_toolchain_failure((result.stdout or "") + (result.stderr or "")) for result in failures):
        return SpellingCheck(namespace_app, "skipped", "lean failed because of the toolchain")
    if "timed out" in output:
        return SpellingCheck(namespace_app, "skipped", "lean timed out; skipping the live check")
    raise BridgeDescriptionError("lean rejected an equivalent spelling:\n" + output.strip())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    describe = commands.add_parser("describe", help="print one narrow bridge application")
    describe.add_argument("source", type=Path, help="Lean file to read")
    describe.add_argument("--target", required=True, help="conclusion that must match exactly")
    describe.add_argument(
        "--known",
        action="append",
        default=[],
        help="premise type that counts as a known declaration; repeat for several",
    )
    commands.add_parser(
        "check-equivalent",
        help="compare the namespace and full-name spellings, elaborating them when lean is available",
    )
    args = parser.parse_args(argv)
    try:
        if args.command == "check-equivalent":
            checked = check_equivalent_spellings()
            sys.stdout.write(format_application(checked.application))
            sys.stdout.write(f"spellings: identical\nlean: {checked.lean}\n")
            if checked.detail:
                sys.stdout.write(f"lean_detail: {checked.detail}\n")
            return 0
        text = args.source.read_text(encoding="utf-8")
        known = set(args.known) if args.known else None
        application = describe_bridge(text, args.target, known)
    except OSError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    except BridgeDescriptionError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    sys.stdout.write(format_application(application))
    return 0


if __name__ == "__main__":
    sys.exit(main())
