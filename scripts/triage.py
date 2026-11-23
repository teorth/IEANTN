#!/usr/bin/env python3
"""Mechanical pull-request triage: compose, queue, integrate, and follow up a verification.

None of this reviews anything. It does the bookkeeping around a review that is easy to get
wrong by hand, and each piece exists because getting it wrong by hand cost something.

    python3 scripts/triage.py compose --worktree ../wt 177 178 200
    python3 scripts/triage.py compose --worktree ../wt --all
    python3 scripts/triage.py queue 237 238 239          # plans; add --execute to merge
    python3 scripts/triage.py integrate --worktree ../wt --branch integrate/foo 210 212
    python3 scripts/triage.py receipt-pr RosserSchoenfeld1962.v2

**`compose` is the part CI cannot do.** CI tests each pull request against `main`; nothing
tests them against each other. Two branches that are each green can still be incompatible --
observed on #225 and #226, which composed into five test failures while both showed green --
and a family of node pull requests conflicts pairwise in `IEANTN/Nodes.lean`, which is
generated and which no contributor can usefully resolve by hand.

`queue` encodes what the branch protection on `main` makes necessary. Required checks are
strict, so every merge puts the rest behind and each pull request must be updated, re-checked
and merged in turn. Four things it does deliberately:

* it waits for `mergeStateStatus` to settle. After a merge GitHub reports `UNKNOWN` while it
  recomputes, and acting on that reads "not behind" from "do not know yet";
* it decides on the status rollup, never on `gh pr checks`' exit code, which is nonzero both
  for a failure and for checks still running;
* it retries a known-flaky *infrastructure* signature against a budget -- a toolchain that
  will not download, a 5xx from GitHub's own API -- and stops the line for anything else. A
  502 inside `receipt provenance` is the network failing to answer, not a bad receipt;
* it merges with a merge commit, never a squash. A fork's pull request is badged **Merged**
  only when its head commit becomes reachable, and a squash discards that.

It also distinguishes "held" from "failed". A pull request that is green, up to date and still
`BLOCKED` is held by a branch policy, and no amount of waiting changes it; the queue says so
and moves on rather than spending its attempts and stopping everything behind it.

Nothing here approves, dispatches a verification, or writes a receipt.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import time

#: Infrastructure failures worth one retry. Every entry is something outside the tree: a
#: download that did not serve, or GitHub answering 5xx to a question the check had to ask.
#: Nothing here can be caused by the branch being wrong, which is the property that makes
#: retrying honest rather than a way of wearing a real failure down.
FLAKE = re.compile(
    r"could not download file from"
    r"|downloading installer"
    r"|curl: \(22\)"
    r"|error: 50[0-9]\b"
    r"|Gateway Time-?out"
    r"|jobs could not be read"
    r"|Server Error \(HTTP 5"
    r"|was not found on this server",
    re.IGNORECASE,
)

PASSED, FAILED, PENDING = "passed", "failed", "pending"


class Shell:
    """Every `git` and `gh` call goes through here, so tests can replace it."""

    def __init__(self, cwd: pathlib.Path) -> None:
        self.cwd = cwd

    def run(self, *argv: str) -> tuple[int, str, str]:
        done = subprocess.run(argv, cwd=self.cwd, capture_output=True, text=True,
                              encoding="utf-8", errors="replace")
        return done.returncode, (done.stdout or "").strip(), (done.stderr or "").strip()

    def git(self, *argv: str) -> tuple[int, str, str]:
        return self.run("git", *argv)

    def gh(self, *argv: str) -> tuple[int, str, str]:
        return self.run("gh", *argv)

    def sleep(self, seconds: float) -> None:
        time.sleep(seconds)


def classify_checks(rollup: list[dict]) -> str:
    """`passed`, `failed` or `pending` for one head's check rollup.

    `gh pr checks` exits nonzero for a failure *and* for checks that are merely still
    running, and treating the second as the first aborted a queue with nothing wrong. The
    rollup says which it is, so the rollup decides.

    An empty rollup is `pending`, not `passed`: a pull request whose workflows have not been
    approved to run reports no checks at all, and that must never read as success.
    """
    if not rollup:
        return PENDING
    states = []
    for entry in rollup:
        conclusion = (entry.get("conclusion") or "").upper()
        status = (entry.get("status") or entry.get("state") or "").upper()
        if conclusion in {"FAILURE", "TIMED_OUT", "CANCELLED", "STARTUP_FAILURE", "ACTION_REQUIRED"}:
            return FAILED
        if conclusion in {"SUCCESS", "SKIPPED", "NEUTRAL"}:
            states.append(PASSED)
        elif status in {"COMPLETED"}:
            states.append(PASSED)
        else:
            states.append(PENDING)
    return PENDING if PENDING in states else PASSED


def is_flake(log: str) -> bool:
    """Whether a failing run's log shows an infrastructure failure rather than a bad branch."""
    return bool(FLAKE.search(log or ""))


def held_by_policy(state: str, checks: str, behind: bool) -> bool:
    """A pull request that cannot merge for a reason waiting will not fix.

    Green, not behind, and still `BLOCKED` means a branch policy is holding it -- a review it
    has not got, most often. The queue reports that and moves on instead of spending every
    attempt on it and stopping the pull requests behind it.
    """
    return state == "BLOCKED" and checks == PASSED and not behind


def _json(shell: Shell, *argv: str) -> object:
    code, out, _ = shell.gh(*argv)
    if code != 0 or not out:
        return None
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return None


def pull_request(shell: Shell, number: int) -> dict:
    """The fields the queue decides on, in one call."""
    data = _json(shell, "pr", "view", str(number), "--json",
                 "number,state,mergeStateStatus,headRefName,headRefOid,"
                 "isCrossRepository,statusCheckRollup,title")
    return data if isinstance(data, dict) else {}


def settled(shell: Shell, number: int, tries: int = 30, pause: float = 10.0) -> str:
    """`mergeStateStatus`, once GitHub stops saying `UNKNOWN`.

    Reading it straight after a merge gives `UNKNOWN` while GitHub recomputes mergeability,
    and `UNKNOWN` is not "clean" -- acting on it merges a branch nobody has established is
    up to date.
    """
    for _ in range(tries):
        state = pull_request(shell, number).get("mergeStateStatus") or ""
        if state and state != "UNKNOWN":
            return state
        shell.sleep(pause)
    return "UNKNOWN"


def wait_for_checks(shell: Shell, number: int, rollup: list[dict]) -> str:
    """Block until this pull request's checks settle, then classify them.

    `gh pr checks --watch` blocks until every check completes. That matters because a Lean build
    here takes about nine minutes: the first version of this polled inside the attempt loop, so
    each wait consumed an attempt and the whole budget expired in three and a half minutes with
    the build still running. The queue then reported "gave up" on two pull requests that were
    perfectly healthy.

    Its exit code is still not consulted -- nonzero means a failure *or* a run that is merely
    incomplete, which is the confusion `classify_checks` exists to resolve -- so the rollup is
    re-read afterwards and decides.

    An empty rollup is the one case not to wait on: a pull request whose workflows have not been
    approved to run has no checks to complete, and `--watch` would block on something that will
    never arrive. That returns `PENDING` and the caller's attempt budget handles it.
    """
    if not rollup:
        return PENDING
    shell.gh("pr", "checks", str(number), "--watch", "--interval", "30")
    return classify_checks(pull_request(shell, number).get("statusCheckRollup") or [])


def failing_run_id(rollup: list[dict]) -> str | None:
    """The Actions run behind the first failing check, if its details URL names one."""
    for entry in rollup:
        if (entry.get("conclusion") or "").upper() != "FAILURE":
            continue
        found = re.search(r"actions/runs/(\d+)", entry.get("detailsUrl") or "")
        if found:
            return found.group(1)
    return None


# --------------------------------------------------------------------------------------- queue


def queue(shell: Shell, numbers: list[int], execute: bool, rerun_budget: int = 6,
          rounds: int = 8, pause: float = 25.0) -> int:
    """Update, re-check and merge each pull request in turn. Returns a process exit code.

    Without `--execute` nothing is merged and nothing is pushed: it reports what each pull
    request's state is and stops. That is the default because this is the one command here
    that changes `main`.
    """
    reruns = 0
    held: list[int] = []
    failed: list[int] = []
    merged: list[int] = []

    for number in numbers:
        facts = pull_request(shell, number)
        if facts.get("state") != "OPEN":
            print(f"SKIP #{number}: {str(facts.get('state')).lower() or 'unreadable'}")
            continue
        print(f"=== #{number}  {facts.get('title', '')[:60]}")

        if not execute:
            # Settle the state here too, briefly. GitHub answers `UNKNOWN` until something
            # asks, so a single read reports "do not know" for a pull request that is
            # perfectly clean, which makes the plan useless for deciding anything.
            state = settled(shell, number, tries=4, pause=3.0)
            rollup = pull_request(shell, number).get("statusCheckRollup") or []
            checks = classify_checks(rollup)
            if held_by_policy(state, checks, False):
                note = ("green and up to date, but held by a branch policy -- most often a "
                        "review it has not got")
            elif state == "UNKNOWN":
                note = f"GitHub has not computed mergeability yet; checks {checks}"
            elif state == "CLEAN" and checks == PASSED:
                note = "ready to merge"
            else:
                note = f"{state.lower()}, checks {checks}"
            print(f"  {note}")
            continue

        done = False
        for attempt in range(1, rounds + 1):
            state = settled(shell, number)
            print(f"  attempt {attempt}: {state}")

            if state == "BEHIND":
                code, _, err = shell.gh("pr", "update-branch", str(number))
                if code != 0:
                    print(f"  ABORT #{number}: update-branch failed: {err[:200]}")
                    failed.append(number)
                    break
                print("  branch updated")
                shell.sleep(pause)
                continue
            if state not in {"CLEAN", "BLOCKED"}:
                print(f"  ABORT #{number}: unexpected state {state}")
                failed.append(number)
                break

            rollup = pull_request(shell, number).get("statusCheckRollup") or []
            checks = wait_for_checks(shell, number, rollup)
            rollup = pull_request(shell, number).get("statusCheckRollup") or []
            if checks == PENDING:
                print("  no checks have started yet")
                shell.sleep(pause)
                continue
            if checks == FAILED:
                run = failing_run_id(rollup)
                log = ""
                if run:
                    _, log, _ = shell.gh("run", "view", run, "--log-failed")
                if run and is_flake(log) and reruns < rerun_budget:
                    reruns += 1
                    print(f"  infrastructure failure; rerunning {run} ({reruns}/{rerun_budget})")
                    shell.gh("run", "rerun", run, "--failed")
                    shell.sleep(pause)
                    continue
                print(f"  ABORT #{number}: checks failed")
                failed.append(number)
                break

            # Mergeability has to be re-read, because `state` above was taken *before* a wait
            # that lasts as long as a Lean build. GitHub reports a pull request blocked on its
            # own pending required checks as `BLOCKED`, and `held_by_policy` reads `BLOCKED` plus
            # green checks as "a branch policy is holding this" -- which is exactly what a pull
            # request looks like the instant its checks go green, if you ask before the wait and
            # answer after it. Deciding from the stale value reports a ready pull request as held
            # and never merges it. Anything not settled goes back round, where `BEHIND` and the
            # unexpected states are handled as above; that costs one attempt, which is what the
            # budget is for.
            state = settled(shell, number)
            if state not in {"CLEAN", "BLOCKED"}:
                print(f"  mergeability moved to {state} while waiting; going round again")
                continue

            if held_by_policy(state, checks, False):
                print(f"  HELD #{number}: green and up to date, but a branch policy holds it. "
                      "Most often a review it has not got.")
                held.append(number)
                break

            # A merge commit, never a squash: a fork's pull request is badged Merged only
            # when its head commit becomes reachable from the default branch.
            code, _, err = shell.gh("pr", "merge", str(number), "--merge")
            if code == 0:
                print(f"  MERGED #{number}")
                merged.append(number)
                done = True
                break
            print(f"  merge refused: {err[:200]}")
            shell.sleep(pause)

        if not done and number not in held and number not in failed:
            print(f"  GAVE UP on #{number} after {rounds} rounds")
            failed.append(number)

    if execute:
        print(f"\nmerged: {merged or 'none'}")
        if held:
            print(f"held by policy: {held}")
        if failed:
            print(f"did not merge: {failed}")
    return 1 if failed else 0


# ------------------------------------------------------------------------------------ worktree


def checked_worktree(path: pathlib.Path, main_checkout: pathlib.Path) -> Shell | None:
    """A shell bound to `path`, refusing anything that is not a separate worktree.

    This guard is here because its absence did real damage: a `;` where `&&` was meant let a
    loop of twenty-three `git merge` calls run in the maintainer's own checkout, on `main`.
    A compose run merges many branches and throws them away, so it must never be able to do
    that anywhere a human keeps work.
    """
    if not path.is_dir():
        print(f"error: {path} is not a directory. Make a worktree first:")
        print(f"  git worktree add {path} origin/main")
        return None
    shell = Shell(path)
    code, top, _ = shell.git("rev-parse", "--show-toplevel")
    if code != 0:
        print(f"error: {path} is not inside a git repository")
        return None
    resolved = pathlib.Path(top).resolve()
    if resolved == main_checkout.resolve():
        print("error: that is the main checkout, not a worktree. Refusing: this command "
              "merges and discards branches.")
        return None
    _, common, _ = shell.git("rev-parse", "--git-common-dir")
    if not common:
        print(f"error: cannot establish that {path} shares this repository")
        return None
    return shell


def open_pull_requests(shell: Shell, limit: int = 100) -> list[int]:
    data = _json(shell, "pr", "list", "--state", "open", "--limit", str(limit),
                 "--json", "number")
    if not isinstance(data, list):
        return []
    return sorted((entry["number"] for entry in data if isinstance(entry, dict)), reverse=True)


def fetch_heads(shell: Shell, numbers: list[int]) -> list[int]:
    """Fetch each pull request's head to a local `pr<n>` ref. Returns the ones that arrived."""
    got = []
    for number in numbers:
        code, _, _ = shell.git("fetch", "origin", f"pull/{number}/head:pr{number}", "-f")
        if code == 0:
            got.append(number)
        else:
            print(f"  cannot fetch #{number}")
    return got


def compose(shell: Shell, numbers: list[int], base: str = "origin/main") -> int:
    """Merge the given pull requests onto one tree, naming those that do not compose.

    Each is also tried alone, because the distinction matters: a branch that conflicts only
    *after* another has landed needs the other author to do nothing, while one that conflicts
    with `base` needs a rebase. The generated umbrellas are the usual reason for the first,
    and `gen-challenges` resolves those -- not the contributor.
    """
    shell.git("fetch", "origin", "-q")
    numbers = fetch_heads(shell, numbers)
    if not numbers:
        print("nothing to compose")
        return 1

    alone_bad: list[int] = []
    for number in numbers:
        shell.git("reset", "--hard", base, "-q")
        code, _, _ = shell.git("merge", "--no-edit", "-q", f"pr{number}")
        if code != 0:
            alone_bad.append(number)
        shell.git("merge", "--abort")

    shell.git("reset", "--hard", base, "-q")
    composed: list[int] = []
    together_bad: list[tuple[int, list[str]]] = []
    for number in numbers:
        code, _, _ = shell.git("merge", "--no-edit", "-q", f"pr{number}")
        if code == 0:
            composed.append(number)
            continue
        _, files, _ = shell.git("diff", "--name-only", "--diff-filter=U")
        together_bad.append((number, [name for name in files.splitlines() if name]))
        shell.git("merge", "--abort")

    print(f"\ncomposes together: {composed or 'none'}")
    for number, files in together_bad:
        kind = "needs a rebase onto " + base if number in alone_bad else "conflicts only in company"
        print(f"  #{number}: {kind}")
        for name in files:
            generated = " (generated -- resolve with gen-challenges)" if is_generated(name) else ""
            print(f"      {name}{generated}")
    shell.git("reset", "--hard", base, "-q")
    return 0


#: Files the generator owns. A conflict here is never a contributor's to resolve.
GENERATED = ("IEANTN/Nodes.lean", "IEANTN/Bridges.lean")


def is_generated(name: str) -> bool:
    return name in GENERATED or bool(re.fullmatch(r"IEANTN/Nodes/[^/]+/[^/]+/Challenge\.lean", name))


# ----------------------------------------------------------------------------------- integrate


def integrate(shell: Shell, numbers: list[int], branch: str, base: str = "origin/main",
              push: bool = False) -> int:
    """Merge several pull requests onto one branch, resolving generated files by regenerating.

    This exists for a family of node pull requests that each merge cleanly onto `main` but
    conflict with one another in `IEANTN/Nodes.lean`. Asking several contributors to rebase in
    turn over a generated file is the wrong shape of work, and the file has no hand-resolvable
    version. Every head commit stays an ancestor, so each pull request is badged Merged when
    this branch lands, and authorship is untouched.

    `git reset` is never used while a merge is in progress. Doing that discards the merge
    state, and the commit that follows has no second parent -- it lands the content while
    silently failing to badge the pull request it came from.
    """
    shell.git("fetch", "origin", "-q")
    numbers = fetch_heads(shell, numbers)
    if not numbers:
        return 1

    code, _, err = shell.git("checkout", "-q", "-B", branch, base)
    if code != 0:
        print(f"error: cannot start {branch}: {err[:200]}")
        return 1

    for number in numbers:
        code, _, _ = shell.git("merge", "--no-edit", f"pr{number}")
        if code == 0:
            print(f"merged #{number}")
            continue
        _, files, _ = shell.git("diff", "--name-only", "--diff-filter=U")
        conflicts = [name for name in files.splitlines() if name]
        if not conflicts or not all(is_generated(name) for name in conflicts):
            print(f"error: #{number} conflicts outside the generated files: {conflicts}")
            shell.git("merge", "--abort")
            return 1
        print(f"#{number}: regenerating {', '.join(conflicts)}")
        code, out, gen_err = shell.run(sys.executable, "scripts/ieantn.py", "gen-challenges")
        if code != 0:
            print(f"error: gen-challenges failed: {(gen_err or out)[:300]}")
            shell.git("merge", "--abort")
            return 1
        shell.git("add", *GENERATED)
        _, left, _ = shell.git("diff", "--name-only", "--diff-filter=U")
        if left.strip():
            print(f"error: still conflicted after regenerating: {left}")
            shell.git("merge", "--abort")
            return 1
        shell.git("commit", "-q", "--no-verify", "-m",
                  f"Merge #{number} into {branch}\n\n"
                  "The conflict was in a generated file, so it is resolved by running\n"
                  "`python scripts/ieantn.py gen-challenges`, not by hand.")
        print(f"merged #{number} (umbrella regenerated)")

    code, out, _ = shell.run(sys.executable, "scripts/ieantn.py", "gen-challenges", "--check")
    if code != 0:
        print(f"error: generated files are not idempotent after integrating:\n{out[:500]}")
        return 1
    print("gen-challenges --check: ok")

    if push:
        code, _, err = shell.git("push", "-q", "origin", f"HEAD:refs/heads/{branch}")
        if code != 0:
            print(f"error: push failed: {err[:200]}")
            return 1
        print(f"pushed {branch}")
    else:
        print(f"\n{branch} is ready locally. Re-run with --push to publish it.")
    return 0


# --------------------------------------------------------------------------------- receipt-pr


def receipt_pr(shell: Shell, node: str, branch: str | None, create: bool = False) -> int:
    """Open the pull request that carries a verification's receipt.

    The receipt job pushes to the branch that was verified, not to the contributor's pull
    request, so that pull request still shows the pre-verification state and merging it would
    land the node without the receipt it just earned. This opens the pull request from the
    branch instead. It is the step that was missed once, and the node went in one commit short.
    """
    if branch is None:
        print("error: name the branch the receipt landed on (--branch)")
        return 1
    _, head, _ = shell.git("ls-remote", "--heads", "origin", branch)
    if not head.strip():
        print(f"error: `origin` has no branch `{branch}`")
        return 1
    receipts = [line for line in shell.git("ls-tree", "--name-only", f"origin/{branch}",
                                           "receipts/")[1].splitlines()
                if node in line]
    if not receipts:
        print(f"warning: no receipt for {node} found on `{branch}`. Has the receipt job run?")
    else:
        print(f"receipts on `{branch}`:")
        for name in receipts:
            print(f"  {name}")
    title = f"{node}: record the Comparator receipt"
    body = (f"Carries the Comparator receipt for `{node}`.\n\n"
            "The receipt job pushes to the branch it verified, not to the originating pull "
            "request, so that pull request still shows the pre-verification state and merging "
            "it would land the node without its receipt. Merging **this** with a merge commit "
            "lands both, and badges the original as merged because its head is an ancestor "
            "here.\n\nA squash would discard that and the original would show as closed.\n")
    if not create:
        print(f"\nwould open: {title}\n  from {branch}\nRe-run with --create to open it.")
        return 0
    code, out, err = shell.gh("pr", "create", "--head", branch, "--base", "main",
                              "--title", title, "--body", body)
    print(out or err)
    return 0 if code == 0 else 1


# ---------------------------------------------------------------------------------------- cli


def main(argv: list[str] | None = None) -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    composed = sub.add_parser("compose", help="which open pull requests compose together")
    composed.add_argument("numbers", nargs="*", type=int)
    composed.add_argument("--all", action="store_true", help="every open pull request")
    composed.add_argument("--worktree", required=True, type=pathlib.Path)

    queued = sub.add_parser("queue", help="update, re-check and merge each in turn")
    queued.add_argument("numbers", nargs="+", type=int)
    queued.add_argument("--execute", action="store_true", help="actually merge")

    joined = sub.add_parser("integrate", help="merge several onto one branch")
    joined.add_argument("numbers", nargs="+", type=int)
    joined.add_argument("--branch", required=True)
    joined.add_argument("--worktree", required=True, type=pathlib.Path)
    joined.add_argument("--push", action="store_true")

    followed = sub.add_parser("receipt-pr", help="open the pull request holding a receipt")
    followed.add_argument("node")
    followed.add_argument("--branch")
    followed.add_argument("--create", action="store_true")

    args = parser.parse_args(argv)
    here = Shell(root)

    if args.command == "queue":
        return queue(here, args.numbers, args.execute)
    if args.command == "receipt-pr":
        return receipt_pr(here, args.node, args.branch, args.create)

    tree = checked_worktree(args.worktree, root)
    if tree is None:
        return 1
    if args.command == "compose":
        numbers = open_pull_requests(here) if args.all else args.numbers
        if not numbers:
            print("name some pull requests, or pass --all")
            return 1
        return compose(tree, numbers)
    return integrate(tree, args.numbers, args.branch, push=args.push)


if __name__ == "__main__":
    raise SystemExit(main())
