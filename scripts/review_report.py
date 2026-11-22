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
    # A finding is untrusted text, not permission to notify users or teams.
    return "- " + body.replace("@", "＠").replace("\n", "\n  ")


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
    if context.get("origin_base_unconfirmed"):
        origin_note = (
            "The workflow event did not identify its originating pull request. "
            if context.get("origin_unidentified") else ""
        )
        lines += [
            origin_note + "This comment is associated by the run's fork, branch and commit; "
            "the analysis's original base is not independently attested. Base-relative "
            "findings are not confirmed for this pull request's current base.",
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
    """The run SHA from a successful pull-request workflow_run event, or None.

    Fork runs can have an empty `pull_requests` array. Resolve the comment target separately
    through the trusted run SHA, never through a number supplied in the artifact.
    `checkout_head` is always false: the SHA is a label, not a ref to execute.
    """
    if not isinstance(event, dict):
        return None
    run = event.get("workflow_run")
    if not isinstance(run, dict):
        return None
    if run.get("conclusion") != "success" or run.get("event") != "pull_request":
        return None
    sha = run.get("head_sha")
    if not isinstance(sha, str) or HEAD_SHA.fullmatch(sha) is None:
        return None
    head_repository = _text(_mapping(run.get("head_repository")).get("full_name"))
    head_branch = _text(run.get("head_branch"))
    if REPO_NAME.fullmatch(head_repository) is None or not head_branch:
        return None
    trusted: dict = {
        "run_head_sha": sha, "checkout_head": False,
        "head_repository": head_repository, "head_branch": head_branch,
    }
    pulls = run.get("pull_requests", [])
    if not isinstance(pulls, list) or len(pulls) > 1:
        return None
    if pulls:
        number = _mapping(pulls[0]).get("number")
        if type(number) is not int or number < 1:
            return None
        trusted["pull_request"] = number
    return trusted


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


def _pull_request_number(
    repo: str, run_head_sha: str, token: str, head_repository: str, head_branch: str,
    expected_number: int | None = None,
) -> int | None:
    """Find one unambiguous association, retaining any trusted event identity.

    A closed association still makes another open PR ambiguous: a shared commit does not
    establish which PR produced the run's base-relative analysis.
    """
    numbers: set[int] = set()
    associated: set[int] = set()
    path: str | None = f"/repos/{repo}/commits/{run_head_sha}/pulls?per_page=100"
    while path is not None:
        page, link = _api("GET", path, None, token)
        if not isinstance(page, list):
            raise ReviewReportError("associated pull-request listing was not a list")
        for pull in page:
            if not isinstance(pull, dict):
                raise ReviewReportError("associated pull request was not an object")
            number = pull.get("number")
            base_repo = _mapping(_mapping(pull.get("base")).get("repo"))
            if type(number) is not int or number < 1 or base_repo.get("full_name") != repo:
                raise ReviewReportError("unexpected associated pull-request identity")
            if pull.get("state") not in {"open", "closed"}:
                raise ReviewReportError("unexpected associated pull-request state")
            associated.add(number)
            head = _mapping(pull.get("head"))
            if (pull["state"] == "open" and head.get("ref") == head_branch
                    and _mapping(head.get("repo")).get("full_name") == head_repository):
                numbers.add(number)
            if len(numbers) > 1:
                raise ReviewReportError("more than one open pull request matches the run commit")
        match = re.search(r"<https://api\.github\.com([^>]+)>; rel=\"next\"", link)
        path = match.group(1) if match else None
    if not numbers:
        return None
    number = next(iter(numbers))
    if len(associated) > 1 or expected_number is not None and number != expected_number:
        raise ReviewReportError("associated pull request is ambiguous or differs from the trusted event")
    return number


def resolve_review_target(event: object, repo: str, token: str) -> tuple[dict, int] | None:
    """Read-only target discovery, also used before acquiring a per-PR comment lock."""
    if REPO_NAME.fullmatch(repo) is None:
        raise ReviewReportError("unexpected repository name")
    trusted = trusted_run(event)
    if trusted is None:
        return None
    if trusted["checkout_head"]:
        raise ReviewReportError("refusing to comment from a plan that checks out the head")
    number = _pull_request_number(
        repo, trusted["run_head_sha"], token, trusted["head_repository"], trusted["head_branch"],
        trusted.get("pull_request"),
    )
    return (trusted, number) if number is not None else None


def post_review(
    event: dict, payload_path: pathlib.Path, repo: str, token: str,
    expected_number: int | None = None,
) -> int:
    """Post or update the comment. Returns 0 when there is nothing to comment on."""
    target = resolve_review_target(event, repo, token)
    if target is None:
        print("no unambiguous pull request matches the trusted run context; not commenting")
        return 0
    trusted, number = target
    if expected_number is not None and (type(expected_number) is not int or number != expected_number):
        raise ReviewReportError("resolved pull request changed after acquiring its comment lock")
    report = load_report_file(payload_path)
    pull, _link = _api("GET", f"/repos/{repo}/pulls/{number}", None, token)
    if _mapping(pull).get("state") != "open":
        print("the associated pull request is no longer open; not commenting")
        return 0
    head = _mapping(_mapping(pull).get("head"))
    if (head.get("ref") != trusted["head_branch"]
            or _mapping(head.get("repo")).get("full_name") != trusted["head_repository"]):
        raise ReviewReportError("pull-request source no longer matches the trusted run")
    comments = _list_comments(repo, number, token)
    context = context_for(pull, trusted["run_head_sha"])
    # A PR number identifies the origin, not the base used by the old analysis.
    context["origin_unidentified"] = "pull_request" not in trusted
    context["origin_base_unconfirmed"] = True
    body = render_review_report(report, context)
    plan = upsert_review_comment(comments, body)
    if plan["action"] == "update":
        _api("PATCH", f"/repos/{repo}/issues/comments/{plan['id']}", {"body": plan["body"]}, token)
        print(f"updated review comment {plan['id']} on pull request {number}")
    else:
        _api(
            "POST", f"/repos/{repo}/issues/{number}/comments",
            {"body": plan["body"]}, token,
        )
        print(f"created review comment on pull request {number}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Post the IEANTN review report comment")
    sub = parser.add_subparsers(dest="command", required=True)
    resolve = sub.add_parser("resolve", help="resolve the comment target without writing to GitHub")
    post = sub.add_parser("post", help="comment under the resolved pull request's workflow lock")
    for command in (resolve, post):
        command.add_argument("--event", required=True, help="path to the workflow event JSON")
        command.add_argument("--repo", required=True, help="owner/name")
    post.add_argument("--payload", required=True, help="path to review-report.json")
    post.add_argument("--expected-pr", type=int, required=True, help="PR number from the read-only resolve job")
    args = parser.parse_args(argv)
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if not token:
        print("error: GH_TOKEN is not set", file=sys.stderr)
        return 1
    event_path = pathlib.Path(args.event)
    try:
        event = json.loads(event_path.read_text(encoding="utf-8"))
        if args.command == "resolve":
            target = resolve_review_target(event, args.repo, token)
            print(f"pull_request={target[1] if target is not None else ''}")
            return 0
        return post_review(event, pathlib.Path(args.payload), args.repo, token, args.expected_pr)
    except (OSError, json.JSONDecodeError, ReviewReportError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
