#!/usr/bin/env python3
"""Write the Palomar project files spinoff still leaves to the caller.

``ieantn.py spinoff`` prints::

    still to do by hand, and deliberately not guessed at:
      1. lakefile.toml -- this needs a pinned git dependency on the source repository
      2. lake-manifest.json -- commit the one Lake resolves
      3. formalization.yaml -- start from the node's, drop `node` and `conclusions`, and
         add a limitation naming each hypothesis

This writer takes over the lakefile and the formalization skeleton only when the caller
passes the pin and the author metadata. It does not run Lake, does not invent a commit
SHA, and does not add a scientific claim. ``node`` and ``conclusions`` are omitted.

    python3 scripts/palomar_project.py --out DIR --plan plan.json \\
        --core-commit SHA --author NAME --source-url URL \\
        --licence Apache-2.0 --review-status unreviewed
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import yaml


class PalomarExportError(Exception):
    """The caller did not supply something this writer is not allowed to invent."""


_SHA = re.compile(r"^[0-9a-fA-F]{40}$")
_REQUIRED = ("core_commit", "author", "source_url", "licence", "review_status")

NO_HYPOTHESIS_LINE = "there are no hypotheses to name in the limitations"


def limitation_sentence(leaf: str) -> str:
    return f"`{leaf}` is a hypothesis of this submission and is not claimed to be proved here."


def limitation_lines(leaves: list[str]) -> list[str]:
    """The lines spinoff would have asked a person to copy, made exact."""
    if not leaves:
        return [NO_HYPOTHESIS_LINE]
    return [f"- {limitation_sentence(leaf)}" for leaf in leaves]


def _clean(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise PalomarExportError(f"missing {field}")
    if "\n" in value or "\r" in value:
        raise PalomarExportError(f"{field} must be a single line")
    return value.strip()


def require_core_commit(value: object) -> str:
    """Accept only a caller-supplied 40-digit SHA."""
    if not isinstance(value, str) or not value.strip():
        raise PalomarExportError("missing core_commit; refusing to invent a commit SHA")
    commit = value.strip()
    if not _SHA.fullmatch(commit):
        raise PalomarExportError(
            f"core commit {commit!r} is not a 40-digit SHA; refusing to invent a commit SHA"
        )
    return commit


def _leaves_of(plan: dict) -> tuple[str, list[str]]:
    if not isinstance(plan, dict):
        raise PalomarExportError("plan must be a JSON object")
    if "conclusion" not in plan:
        raise PalomarExportError("missing conclusion")
    conclusion = _clean(plan.get("conclusion"), "conclusion")
    if "leaves" not in plan:
        raise PalomarExportError("missing leaves")
    leaves = plan["leaves"]
    if not isinstance(leaves, list) or not all(isinstance(leaf, str) and leaf.strip() for leaf in leaves):
        raise PalomarExportError("leaves must be a list of conclusion keys")
    return conclusion, [leaf.strip() for leaf in leaves]


def _metadata(metadata: dict) -> dict[str, str]:
    if not isinstance(metadata, dict):
        raise PalomarExportError("metadata must be an object")
    missing = [field for field in _REQUIRED if field not in metadata]
    if missing:
        raise PalomarExportError("missing " + ", ".join(missing))
    commit = require_core_commit(metadata.get("core_commit"))
    author = _clean(metadata.get("author"), "author")
    source_url = _clean(metadata.get("source_url"), "source_url")
    licence = _clean(metadata.get("licence"), "licence")
    review_status = _clean(metadata.get("review_status"), "review_status")
    for field, value in (
        ("source_url", source_url),
        ("licence", licence),
        ("author", author),
        ("review_status", review_status),
    ):
        if '"' in value or "\\" in value:
            raise PalomarExportError(f"{field} contains a quote or backslash this writer will not rewrite")
    return {
        "core_commit": commit,
        "author": author,
        "source_url": source_url,
        "licence": licence,
        "review_status": review_status,
    }


def _lakefile(source_url: str, commit: str) -> str:
    return (
        "# Pinned with the commit the caller passed in. Nothing here chooses a revision.\n"
        "name = \"ieantn_spinoff\"\n"
        "defaultTargets = [\"Challenge\", \"Solution\"]\n"
        "\n"
        "[[require]]\n"
        "name = \"IEANTN\"\n"
        f"git = \"{source_url}\"\n"
        f"rev = \"{commit}\"\n"
        "\n"
        "[[lean_lib]]\n"
        "name = \"Challenge\"\n"
        "roots = [\"Challenge\"]\n"
        "\n"
        "[[lean_lib]]\n"
        "name = \"Solution\"\n"
        "roots = [\"Solution\"]\n"
    )


def _formalization(conclusion: str, leaves: list[str], fields: dict[str, str]) -> str:
    limitations = (
        [limitation_sentence(leaf) for leaf in leaves]
        if leaves
        else [
            NO_HYPOTHESIS_LINE,
            "This skeleton does not claim the conclusion is proved.",
        ]
    )
    document = {
        "version": "v0.4",
        "project": {
            "name": f"Spin-off of {conclusion}",
            "description": (
                f"Generated skeleton for `{conclusion}`, pinned to the caller-supplied "
                f"core commit {fields['core_commit']}. Author, source URL, licence, and "
                "review status were supplied by the caller. This file does not add a "
                "scientific claim and does not assert that a hypothesis is proved."
            ),
            "authors": [fields["author"]],
            "license": fields["licence"],
            "responsible_maintainers": [fields["author"]],
        },
        "sources": [
            {
                "title": "Caller-supplied source",
                "authors": [fields["author"]],
                "type": "repository",
                "id": fields["source_url"],
                "url": fields["source_url"],
                "relationship": "formalizes",
            }
        ],
        "review": {"status": fields["review_status"]},
        "limitations": limitations,
        "pin": {
            "core_commit": fields["core_commit"],
            "source_url": fields["source_url"],
        },
    }
    header = (
        "# Skeleton only. The pin and the author metadata were supplied by the caller.\n"
        "# This file does not add a scientific claim.\n"
        "# `node` and `conclusions` are omitted on purpose.\n"
        "# lake-manifest.json is not written; this tool does not run Lake.\n"
    )
    body = yaml.safe_dump(document, allow_unicode=True, sort_keys=False)
    return header + body


def render_report(conclusion: str, leaves: list[str], out: Path) -> str:
    lines = [
        f"wrote {out / 'lakefile.toml'}",
        f"wrote {out / 'formalization.yaml'}",
        "",
        "limitation lines for the leaves:",
        *[f"  {line}" for line in limitation_lines(leaves)],
        "",
        "still to do by hand, and deliberately not guessed at:",
        "  1. lake-manifest.json -- commit the one Lake resolves",
        "  2. validate: see the `palomar-submission` skill for running Palomar's own validator",
        "",
        f"conclusion: {conclusion}",
        "Lake was not run. No commit SHA was invented.",
    ]
    return "\n".join(lines) + "\n"


def write_project(out: Path, plan: dict, metadata: dict) -> str:
    """Write ``lakefile.toml`` and ``formalization.yaml``. Return the printed report."""
    conclusion, leaves = _leaves_of(plan)
    fields = _metadata(metadata)
    out.mkdir(parents=True, exist_ok=True)
    (out / "lakefile.toml").write_text(
        _lakefile(fields["source_url"], fields["core_commit"]),
        encoding="utf-8",
        newline="\n",
    )
    (out / "formalization.yaml").write_text(
        _formalization(conclusion, leaves, fields),
        encoding="utf-8",
        newline="\n",
    )
    if (out / "lake-manifest.json").exists():
        raise PalomarExportError("refusing to replace an existing lake-manifest.json; Lake was not run")
    return render_report(conclusion, leaves, out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--plan", required=True, type=Path, help="JSON object with conclusion and leaves")
    parser.add_argument("--core-commit")
    parser.add_argument("--author")
    parser.add_argument("--source-url")
    parser.add_argument("--licence")
    parser.add_argument("--review-status")
    args = parser.parse_args(argv)
    supplied = {
        "core_commit": args.core_commit,
        "author": args.author,
        "source_url": args.source_url,
        "licence": args.licence,
        "review_status": args.review_status,
    }
    try:
        plan = json.loads(args.plan.read_text(encoding="utf-8"))
        report = write_project(args.out, plan, supplied)
    except (OSError, json.JSONDecodeError, PalomarExportError, yaml.YAMLError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    sys.stdout.write(report)
    return 0


if __name__ == "__main__":
    sys.exit(main())
