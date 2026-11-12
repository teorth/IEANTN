#!/usr/bin/env python3
"""Render the network-impact report and update the one pull-request comment that carries it.

`diff` already decides what a branch degrades. This module does not repeat that analysis and it
does not run Lean. It formats a JSON payload (head SHA, findings, truncated flag) and decides
whether to create or update the single comment whose body starts with the marker.

The comment workflow checks out the default branch, reads the artifact CI uploaded, and posts
with the workflow's own token. A pull-request head is a label in that payload, not a ref to
build.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import sys
import urllib.error
import urllib.request

MARKER = "<!-- ieantn-review-report -->"
HEAD_SHA = re.compile(r"^[0-9a-f]{40}$")
LEVELS = ("breaking", "degraded", "informational")
HEADINGS = {
    "breaking": "### Breaking",
    "degraded": "### Degraded",
    "informational": "### Informational",
}
MAX_FINDINGS = 40
MAX_BODY = 4000
MAX_COMMENT = 60000
MAX_PAYLOAD_BYTES = 1_000_000
REPO_NAME = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")


class ReviewReportError(ValueError):
    """The payload or the comment list is not something this workflow should post."""


def normalize_report(raw: object) -> dict:
    """Accept only the recorded analysis, and cap it.

    A pull request can upload whatever JSON it likes. Strings stay strings: nothing here is
    executed. Oversized input is cut down and the truncated flag is forced on, so the comment
    cannot grow without saying so.
    """
    if not isinstance(raw, dict):
        raise ReviewReportError("report must be a JSON object")
    extra = sorted(set(raw) - {"head_sha", "findings", "truncated"})
    if extra:
        raise ReviewReportError(f"unexpected report keys: {', '.join(extra)}")
    sha = raw.get("head_sha")
    if not isinstance(sha, str) or HEAD_SHA.fullmatch(sha) is None:
        raise ReviewReportError("head_sha must be 40 lowercase hex characters")
    if not isinstance(raw.get("truncated"), bool):
        raise ReviewReportError("truncated must be a boolean")
    findings = raw.get("findings")
    if not isinstance(findings, list):
        raise ReviewReportError("findings must be a list")
    truncated = raw["truncated"]
    if len(findings) > MAX_FINDINGS:
        findings = findings[:MAX_FINDINGS]
        truncated = True
    kept: list[dict[str, str]] = []
    for item in findings:
        if not isinstance(item, dict):
            raise ReviewReportError("each finding must be an object")
        item_extra = sorted(set(item) - {"level", "body"})
        if item_extra:
            raise ReviewReportError(
                f"a finding may only have level and body, not {', '.join(item_extra)}"
            )
        level = item.get("level")
        body = item.get("body")
        if level not in LEVELS:
            raise ReviewReportError(f"unknown finding level {level!r}")
        if not isinstance(body, str) or not body.strip():
            raise ReviewReportError("finding body must be a non-empty string")
        if len(body) > MAX_BODY:
            body = body[:MAX_BODY].rstrip() + "…"
            truncated = True
        kept.append({"level": level, "body": body})
    return {"head_sha": sha, "findings": kept, "truncated": truncated}


def build_ci_payload(
    head_sha: str, errors: list[str], warnings: list[str], notes: list[str]
) -> dict:
    """The artifact `diff` uploads. Truncation is applied here, before the file is written."""
    findings = (
        [{"level": "breaking", "body": item} for item in errors]
        + [{"level": "degraded", "body": item} for item in warnings]
        + [{"level": "informational", "body": item} for item in notes]
    )
    return normalize_report({"head_sha": head_sha, "findings": findings, "truncated": False})


def _bullet(body: str) -> str:
    return "- " + body.replace("\n", "\n  ")


def render_review_report(payload: object, context: dict) -> str:
    """Markdown for the pull-request comment. The marker is the first line, with nothing before it."""
    report = normalize_report(payload)
    described = report["head_sha"]
    run_sha = context.get("run_head_sha") or ""
    current = context.get("current_head_sha") or ""
    if isinstance(run_sha, str) and HEAD_SHA.fullmatch(run_sha):
        described = run_sha
    lines = [
        MARKER,
        "",
        "## Network impact",
        "",
        f"Bound to head `{described}`.",
        "",
    ]
    if described != report["head_sha"]:
        lines += [
            f"The artifact names `{report['head_sha']}`, which is not the head SHA of the "
            "workflow run. The run SHA above is the one CI checked out.",
            "",
        ]
    head_repo = context.get("head_repository") or ""
    base_repo = context.get("base_repository") or ""
    if head_repo and base_repo and head_repo != base_repo:
        lines += [
            f"This pull request is from `{head_repo}`, a fork of `{base_repo}`. "
            "The comment was rendered from the CI artifact. This workflow did not check out "
            "that head and did not execute its Lean.",
            "",
        ]
    if isinstance(current, str) and HEAD_SHA.fullmatch(current):
        if current != described:
            lines += [
                f"**Stale.** This report describes `{described}`, but the pull request head "
                f"is now `{current}`.",
                "",
            ]
    else:
        lines += [
            "The pull request's current head SHA could not be read, so this report is not "
            "known to be current.",
            "",
        ]
    if report["truncated"]:
        lines += ["Findings were truncated. This comment is not the complete analysis.", ""]
    grouped = {level: [] for level in LEVELS}
    for finding in report["findings"]:
        grouped[finding["level"]].append(finding["body"])
    if not any(grouped.values()):
        lines += ["No change to any statement, dependency, or receipt.", ""]
    for level in LEVELS:
        items = grouped[level]
        if not items:
            continue
        lines += [HEADINGS[level], ""]
        lines += [_bullet(item) for item in items]
        lines.append("")
    text = "\n".join(lines).rstrip() + "\n"
    if len(text) > MAX_COMMENT:
        note = "\n\nFindings were truncated. This comment is not the complete analysis.\n"
        text = text[: MAX_COMMENT - len(note)].rstrip() + note
    if not text.startswith(MARKER + "\n"):
        raise ReviewReportError("the rendered comment lost its marker")
    return text


def comment_is_review_report(body: object) -> bool:
    """True only when the marker is the start of the comment, not a later quotation of it."""
    if not isinstance(body, str):
        return False
    return body.lstrip("\ufeff").lstrip().startswith(MARKER)


def upsert_review_comment(comments: list[dict], body: str) -> dict:
    """Update the earliest marker comment, or create one. Never touch a comment without the marker.

    A rerun of the same pull request therefore edits the comment already on the thread. It does
    not add a second one.
    """
    if not comment_is_review_report(body):
        raise ReviewReportError("refusing to post a comment that does not start with the review marker")
    matches: list[dict] = []
    for comment in comments:
        if isinstance(comment, dict) and comment_is_review_report(comment.get("body")):
            matches.append(comment)
    if not matches:
        return {"action": "create", "body": body}
    chosen = min(matches, key=lambda comment: int(comment["id"]))
    return {"action": "update", "id": int(chosen["id"]), "body": body}


def trusted_run(event: object) -> dict | None:
    """The pull request number and run SHA from a workflow_run event, or None if this run is not one.

    `checkout_head` is always false. The head SHA is recorded so the comment can name it. It is
    not a ref, and a fork-shaped payload does not change that.
    """
    if not isinstance(event, dict):
        return None
    run = event.get("workflow_run")
    if not isinstance(run, dict):
        return None
    if run.get("conclusion") != "success" or run.get("event") != "pull_request":
        return None
    pulls = run.get("pull_requests")
    if not isinstance(pulls, list) or not pulls or not isinstance(pulls[0], dict):
        return None
    number = pulls[0].get("number")
    sha = run.get("head_sha")
    if not isinstance(number, int) or isinstance(number, bool) or number < 1:
        return None
    if not isinstance(sha, str) or HEAD_SHA.fullmatch(sha) is None:
        return None
    return {"pull_request": number, "run_head_sha": sha, "checkout_head": False}


def _mapping(value: object) -> dict:
    return value if isinstance(value, dict) else {}


def _text(value: object) -> str:
    return value if isinstance(value, str) else ""


def context_for(pull: object, run_head_sha: str) -> dict:
    """Comment context from the pull-request API object. Missing repo names stay empty."""
    record = _mapping(pull)
    head = _mapping(record.get("head"))
    base = _mapping(record.get("base"))
    head_repo = _mapping(head.get("repo"))
    base_repo = _mapping(base.get("repo"))
    return {
        "current_head_sha": _text(head.get("sha")),
        "run_head_sha": run_head_sha,
        "head_repository": _text(head_repo.get("full_name")),
        "base_repository": _text(base_repo.get("full_name")),
    }


def load_report_file(path: pathlib.Path) -> dict:
    """Read one artifact file. A symlink is refused so the artifact cannot point at another path."""
    if path.name != "review-report.json":
        raise ReviewReportError("refusing to read a report whose name is not review-report.json")
    if path.is_symlink() or not path.is_file():
        raise ReviewReportError(f"review report is not a regular file: {path}")
    if path.stat().st_size > MAX_PAYLOAD_BYTES:
        raise ReviewReportError("review report exceeds the size cap")
    return normalize_report(json.loads(path.read_text(encoding="utf-8")))


def _api(method: str, path: str, body: dict | None, token: str) -> tuple[object, str]:
    request = urllib.request.Request(
        "https://api.github.com" + path, data=None if body is None else json.dumps(body).encode(),
        method=method,
    )
    request.add_header("Authorization", f"Bearer {token}")
    request.add_header("Accept", "application/vnd.github+json")
    request.add_header("X-GitHub-Api-Version", "2022-11-28")
    if body is not None:
        request.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            raw = response.read()
            link = response.headers.get("Link", "")
            return (json.loads(raw) if raw else {}, link)
    except urllib.error.HTTPError as error:
        detail = error.read().decode("utf-8", errors="replace")[:500]
        raise ReviewReportError(f"GitHub API {method} {path} returned {error.code}: {detail}") from None


def _list_comments(repo: str, number: int, token: str) -> list[dict]:
    comments: list[dict] = []
    path: str | None = f"/repos/{repo}/issues/{number}/comments?per_page=100"
    while path is not None:
        page, link = _api("GET", path, None, token)
        if not isinstance(page, list):
            raise ReviewReportError("comment listing was not a list")
        comments.extend(item for item in page if isinstance(item, dict))
        match = re.search(r"<https://api\.github\.com([^>]+)>; rel=\"next\"", link)
        path = match.group(1) if match else None
    return comments


def post_review(event: dict, payload_path: pathlib.Path, repo: str, token: str) -> int:
    """Post or update the comment. Returns 0 when there is nothing to comment on."""
    if REPO_NAME.fullmatch(repo) is None:
        raise ReviewReportError("unexpected repository name")
    trusted = trusted_run(event)
    if trusted is None:
        print("not a successful pull-request run with an associated pull request; not commenting")
        return 0
    if trusted["checkout_head"]:
        raise ReviewReportError("refusing to comment from a plan that checks out the head")
    report = load_report_file(payload_path)
    pull, _link = _api("GET", f"/repos/{repo}/pulls/{trusted['pull_request']}", None, token)
    comments = _list_comments(repo, trusted["pull_request"], token)
    body = render_review_report(report, context_for(pull, trusted["run_head_sha"]))
    plan = upsert_review_comment(comments, body)
    if plan["action"] == "update":
        _api("PATCH", f"/repos/{repo}/issues/comments/{plan['id']}", {"body": plan["body"]}, token)
        print(f"updated review comment {plan['id']} on pull request {trusted['pull_request']}")
    else:
        _api(
            "POST", f"/repos/{repo}/issues/{trusted['pull_request']}/comments",
            {"body": plan["body"]}, token,
        )
        print(f"created review comment on pull request {trusted['pull_request']}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Post the IEANTN review report comment")
    sub = parser.add_subparsers(dest="command", required=True)
    post = sub.add_parser("post", help="comment on the pull request from a workflow_run event")
    post.add_argument("--event", required=True, help="path to the workflow event JSON")
    post.add_argument("--payload", required=True, help="path to review-report.json")
    post.add_argument("--repo", required=True, help="owner/name")
    args = parser.parse_args(argv)
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if not token:
        print("error: GH_TOKEN is not set", file=sys.stderr)
        return 1
    event_path = pathlib.Path(args.event)
    try:
        event = json.loads(event_path.read_text(encoding="utf-8"))
        return post_review(event, pathlib.Path(args.payload), args.repo, token)
    except (OSError, json.JSONDecodeError, ReviewReportError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
