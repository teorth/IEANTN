"""The decisions `triage.py` makes, and the four ways the hand-written version got them wrong.

Each case here is a bug that happened. They are kept as tests rather than as comments because
every one of them looked like a correct reading of an ambiguous signal at the time, and the
next person to touch this will find them equally plausible.
"""
import contextlib
import importlib.util
import io
import json
import pathlib
import sys
import unittest

_SPEC = importlib.util.spec_from_file_location(
    "triage", pathlib.Path(__file__).resolve().parent.parent / "scripts" / "triage.py")
assert _SPEC is not None and _SPEC.loader is not None
triage = importlib.util.module_from_spec(_SPEC)
sys.modules["triage"] = triage
_SPEC.loader.exec_module(triage)


def rollup(*pairs: tuple[str, str]) -> list[dict]:
    """A status rollup from `(status, conclusion)` pairs, as `gh pr view` returns it."""
    return [{"name": f"check{index}", "status": status, "conclusion": conclusion}
            for index, (status, conclusion) in enumerate(pairs)]


class TestClassifyChecks(unittest.TestCase):
    """`gh pr checks` exits nonzero for a failure and for checks still running alike.

    Treating the second as the first aborted a ten-pull-request queue on its first entry,
    while the build it was waiting for went on to pass.
    """

    def test_all_successful_is_passed(self) -> None:
        self.assertEqual(
            triage.classify_checks(rollup(("COMPLETED", "SUCCESS"), ("COMPLETED", "SUCCESS"))),
            triage.PASSED)

    def test_one_still_running_is_pending_not_failed(self) -> None:
        self.assertEqual(
            triage.classify_checks(rollup(("COMPLETED", "SUCCESS"), ("IN_PROGRESS", None))),
            triage.PENDING)

    def test_a_queued_check_is_pending(self) -> None:
        self.assertEqual(triage.classify_checks(rollup(("QUEUED", None))), triage.PENDING)

    def test_a_failure_is_failed_even_beside_successes(self) -> None:
        self.assertEqual(
            triage.classify_checks(rollup(("COMPLETED", "SUCCESS"), ("COMPLETED", "FAILURE"))),
            triage.FAILED)

    def test_a_cancelled_check_is_failed(self) -> None:
        self.assertEqual(triage.classify_checks(rollup(("COMPLETED", "CANCELLED"))),
                         triage.FAILED)

    def test_an_empty_rollup_is_pending_not_passed(self) -> None:
        """A first-time contributor's pull request reports no checks until someone approves
        the workflow run. Reading "no checks" as "nothing failed" would merge it unbuilt."""
        self.assertEqual(triage.classify_checks([]), triage.PENDING)

    def test_a_skipped_check_does_not_block(self) -> None:
        self.assertEqual(
            triage.classify_checks(rollup(("COMPLETED", "SKIPPED"), ("COMPLETED", "SUCCESS"))),
            triage.PASSED)


class TestFlakeRecognition(unittest.TestCase):
    """Retrying is only honest for a failure the branch cannot have caused."""

    def test_the_toolchain_tarball_not_serving_is_a_flake(self) -> None:
        self.assertTrue(triage.is_flake(
            "error: could not download file from https://releases.lean-lang.org/..."))

    def test_the_elan_installer_failing_is_a_flake(self) -> None:
        """The first pattern only matched the tarball, so this signature stopped the line."""
        self.assertTrue(triage.is_flake("curl: (22) The requested URL returned error: 504"))

    def test_a_5xx_while_reading_a_receipt_s_run_is_a_flake(self) -> None:
        """`receipt provenance` asks GitHub about each receipt's run. A 502 there means the
        question went unanswered, not that the receipt is bad -- and it failed #238."""
        self.assertTrue(triage.is_flake(
            "receipts/Chebyshev.v1.psi_upper.json: run 36502365219 jobs could not be read: "
            "gh: Server Error (HTTP 502)"))

    def test_a_real_lean_error_is_not_a_flake(self) -> None:
        self.assertFalse(triage.is_flake(
            "IEANTN/Nodes/A/v1/Conclusions.lean:12:4: error: unknown identifier 'foo'"))

    def test_a_failing_test_is_not_a_flake(self) -> None:
        self.assertFalse(triage.is_flake("FAILED (errors=1)\nAssertionError: 3 != 4"))

    def test_the_word_error_alone_is_not_a_flake(self) -> None:
        self.assertFalse(triage.is_flake("error: check failed"))


class TestHeldByPolicy(unittest.TestCase):
    """Green, up to date and still BLOCKED is not something waiting fixes.

    Observed on two pull requests whose required checks all passed: the queue spent fourteen
    rounds on the first and then aborted, taking nine others down with it.
    """

    def test_green_and_blocked_is_held(self) -> None:
        self.assertTrue(triage.held_by_policy("BLOCKED", triage.PASSED, behind=False))

    def test_blocked_while_checks_run_is_not_held(self) -> None:
        self.assertFalse(triage.held_by_policy("BLOCKED", triage.PENDING, behind=False))

    def test_blocked_and_behind_is_not_held(self) -> None:
        self.assertFalse(triage.held_by_policy("BLOCKED", triage.PASSED, behind=True))

    def test_clean_is_not_held(self) -> None:
        self.assertFalse(triage.held_by_policy("CLEAN", triage.PASSED, behind=False))


class TestGeneratedFiles(unittest.TestCase):
    """Which conflicts are the generator's to resolve rather than a contributor's."""

    def test_the_node_umbrella_is_generated(self) -> None:
        self.assertTrue(triage.is_generated("IEANTN/Nodes.lean"))

    def test_the_bridge_umbrella_is_generated(self) -> None:
        self.assertTrue(triage.is_generated("IEANTN/Bridges.lean"))

    def test_a_challenge_is_generated(self) -> None:
        self.assertTrue(triage.is_generated("IEANTN/Nodes/FKS/v3/Challenge.lean"))

    def test_a_conclusion_is_not(self) -> None:
        self.assertFalse(triage.is_generated("IEANTN/Nodes/FKS/v3/Conclusions.lean"))

    def test_metadata_is_not(self) -> None:
        self.assertFalse(triage.is_generated("IEANTN/Nodes/FKS/v3/formalization.yaml"))

    def test_a_solution_is_not(self) -> None:
        self.assertFalse(triage.is_generated("Solutions/FKS.v3/Solution.lean"))


class FakeShell:
    """Records what was asked and answers from a script of replies."""

    def __init__(self, replies: dict[str, list[tuple[int, str, str]]] | None = None) -> None:
        self.replies = replies or {}
        self.calls: list[tuple[str, ...]] = []
        self.slept = 0.0

    def _answer(self, argv: tuple[str, ...]) -> tuple[int, str, str]:
        self.calls.append(argv)
        for key, queued in self.replies.items():
            if key in " ".join(argv) and queued:
                return queued.pop(0)
        return 0, "", ""

    def run(self, *argv: str) -> tuple[int, str, str]:
        return self._answer(argv)

    def git(self, *argv: str) -> tuple[int, str, str]:
        return self._answer(("git",) + argv)

    def gh(self, *argv: str) -> tuple[int, str, str]:
        return self._answer(("gh",) + argv)

    def sleep(self, seconds: float) -> None:
        self.slept += seconds


def quietly(function, *args, **kwargs):
    """Run it with its progress printing captured; these tests assert on calls, not prose."""
    printed = io.StringIO()
    with contextlib.redirect_stdout(printed):
        return function(*args, **kwargs)


def view(state: str, checks: list[dict], pr_state: str = "OPEN") -> tuple[int, str, str]:
    return 0, json.dumps({"number": 1, "state": pr_state, "mergeStateStatus": state,
                          "statusCheckRollup": checks, "title": "t"}), ""


class TestSettled(unittest.TestCase):
    def test_unknown_is_waited_out(self) -> None:
        """Straight after a merge GitHub reports UNKNOWN while it recomputes. Reading that as
        a state is how a branch got merged that nobody had established was up to date."""
        shell = FakeShell({"pr view": [view("UNKNOWN", []), view("UNKNOWN", []),
                                       view("BEHIND", [])]})
        self.assertEqual(triage.settled(shell, 1, tries=5, pause=0.0), "BEHIND")

    def test_persistent_unknown_is_reported_not_guessed(self) -> None:
        shell = FakeShell({"pr view": [view("UNKNOWN", []) for _ in range(4)]})
        self.assertEqual(triage.settled(shell, 1, tries=3, pause=0.0), "UNKNOWN")


class TestQueuePlanning(unittest.TestCase):
    """Without --execute the queue must not merge, update a branch, or push."""

    def test_planning_merges_nothing(self) -> None:
        shell = FakeShell({"pr view": [view("CLEAN", rollup(("COMPLETED", "SUCCESS")))]})
        self.assertEqual(quietly(triage.queue, shell, [1], execute=False), 0)
        joined = [" ".join(call) for call in shell.calls]
        self.assertFalse([call for call in joined if "pr merge" in call])
        self.assertFalse([call for call in joined if "update-branch" in call])

    def test_a_closed_pull_request_is_skipped(self) -> None:
        shell = FakeShell({"pr view": [view("CLEAN", [], pr_state="MERGED")]})
        self.assertEqual(quietly(triage.queue, shell, [1], execute=False), 0)


class TestQueueExecution(unittest.TestCase):
    def test_a_held_pull_request_does_not_fail_the_run(self) -> None:
        """It is reported and stepped over: the ones behind it are not its hostages."""
        green = rollup(("COMPLETED", "SUCCESS"))
        shell = FakeShell({"pr view": [view("BLOCKED", green)] * 6})
        self.assertEqual(
            quietly(triage.queue, shell, [1], execute=True, rounds=2, pause=0.0), 0)
        self.assertFalse([c for c in shell.calls if "pr merge" in " ".join(c)],
                         "a held pull request must not be merged")

    def test_a_real_failure_stops_that_pull_request(self) -> None:
        red = [{"name": "b", "status": "COMPLETED", "conclusion": "FAILURE",
                "detailsUrl": "https://github.com/o/r/actions/runs/99/job/1"}]
        shell = FakeShell({
            "pr view": [view("CLEAN", red)] * 6,
            "run view": [(0, "error: unknown identifier 'foo'", "")] * 6,
        })
        self.assertEqual(
            quietly(triage.queue, shell, [1], execute=True, rounds=2, pause=0.0), 1)

    def test_an_infrastructure_failure_is_rerun_within_budget(self) -> None:
        red = [{"name": "b", "status": "COMPLETED", "conclusion": "FAILURE",
                "detailsUrl": "https://github.com/o/r/actions/runs/99/job/1"}]
        shell = FakeShell({
            "pr view": [view("CLEAN", red)] * 8,
            "run view": [(0, "curl: (22) The requested URL returned error: 504", "")] * 8,
        })
        quietly(triage.queue, shell, [1], execute=True, rerun_budget=1, rounds=3, pause=0.0)
        reruns = [c for c in shell.calls if "run rerun" in " ".join(c)]
        self.assertEqual(len(reruns), 1, "the budget must cap retries, not merely slow them")

    def test_the_merge_is_never_a_squash(self) -> None:
        """A fork's pull request is badged Merged only when its head becomes reachable."""
        green = rollup(("COMPLETED", "SUCCESS"))
        shell = FakeShell({"pr view": [view("CLEAN", green)] * 4})
        quietly(triage.queue, shell, [1], execute=True, rounds=2, pause=0.0)
        merges = [" ".join(c) for c in shell.calls if "pr merge" in " ".join(c)]
        self.assertTrue(merges)
        for call in merges:
            self.assertIn("--merge", call)
            self.assertNotIn("--squash", call)
            self.assertNotIn("--rebase", call)


class TestWaitingDoesNotSpendTheBudget(unittest.TestCase):
    """A queue must be able to outlast the build it is waiting for.

    The first version polled for pending checks inside the attempt loop, so every wait consumed an
    attempt: with eight attempts and a twenty-five second pause it gave up after three and a half
    minutes, while a Lean build here takes about nine. It reported "gave up" on two healthy pull
    requests. Waiting now blocks in `gh pr checks --watch` and costs no attempt.
    """

    def test_a_long_build_is_waited_out_not_counted(self) -> None:
        green = rollup(("COMPLETED", "SUCCESS"))
        shell = FakeShell({"pr view": [view("CLEAN", green)] * 8})
        self.assertEqual(
            quietly(triage.queue, shell, [1], execute=True, rounds=2, pause=0.0), 0)
        watched = [c for c in shell.calls if "--watch" in c]
        self.assertTrue(watched, "the queue must block on `gh pr checks --watch`")
        self.assertTrue([c for c in shell.calls if "pr merge" in " ".join(c)])

    def test_an_empty_rollup_is_not_watched(self) -> None:
        """A first-time contributor's pull request has no checks to complete, so `--watch` would
        block on something that never arrives."""
        shell = FakeShell({"pr view": [view("CLEAN", [])] * 8})
        quietly(triage.queue, shell, [1], execute=True, rounds=2, pause=0.0)
        self.assertFalse([c for c in shell.calls if "--watch" in c],
                         "an empty rollup must not be watched")
        self.assertFalse([c for c in shell.calls if "pr merge" in " ".join(c)],
                         "and nothing may be merged on no checks at all")


class TestWorktreeGuard(unittest.TestCase):
    """A compose run merges and discards branches, so it must never run where work lives.

    Without this guard, a `;` where `&&` was meant put twenty-three merges into the
    maintainer's own checkout, on `main`.
    """

    def test_a_missing_directory_is_refused(self) -> None:
        self.assertIsNone(quietly(triage.checked_worktree,
                                  pathlib.Path("does-not-exist-anywhere"), pathlib.Path.cwd()))

    def test_the_main_checkout_is_refused(self) -> None:
        root = pathlib.Path(triage.__file__).resolve().parent.parent
        self.assertIsNone(quietly(triage.checked_worktree, root, root))


class TestFailingRunId(unittest.TestCase):
    def test_the_run_is_read_from_the_details_url(self) -> None:
        self.assertEqual(triage.failing_run_id([
            {"conclusion": "SUCCESS", "detailsUrl": "https://x/actions/runs/1"},
            {"conclusion": "FAILURE", "detailsUrl": "https://x/actions/runs/4242/job/7"},
        ]), "4242")

    def test_no_failure_means_no_run(self) -> None:
        self.assertIsNone(triage.failing_run_id(
            [{"conclusion": "SUCCESS", "detailsUrl": "https://x/actions/runs/1"}]))

    def test_a_failure_without_a_run_url_is_not_invented(self) -> None:
        self.assertIsNone(triage.failing_run_id(
            [{"conclusion": "FAILURE", "detailsUrl": "https://example.test/elsewhere"}]))


if __name__ == "__main__":
    unittest.main()
