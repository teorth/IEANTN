"""One verification run may cover several nodes, and what then binds each receipt to it.

`verify.yml` takes a list of nodes so that a batch costs one approval rather than one each, which
means several receipts legitimately cite the same run. The rule that used to stop a forged receipt
-- one run, one node -- would reject exactly that. What replaces it is not weaker: the run's own
job names say which nodes it verified, GitHub records them from the dispatch rather than from the
receipt, and the check is per node. The older rule stays for runs that predate the convention and
so have nothing better.

The forgery being prevented throughout is the same one: copying the run URL out of a real receipt
into a fabricated one for a different node.
"""
import contextlib
import io
import json
import unittest.mock

from test_ieantn import FixtureRepo, ieantn

RUN = "https://github.com/teorth/IEANTN/actions/runs/123"
OTHER_RUN = "https://github.com/teorth/IEANTN/actions/runs/456"


class BatchedReceipts(FixtureRepo):
    def receipt(self, conclusion: str, url: str = RUN) -> None:
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / f"{conclusion}.json").write_text(
            json.dumps({"conclusion": conclusion, "run": {"workflow_run": url}}),
            encoding="utf-8")

    def answered_by(self, job_names: list[str], conclusion: str = "success"):
        """`subprocess.run` as the check sees it: a remote, a run, and that run's job names."""
        calls: list[str] = []

        def response(args, **kwargs):
            if args[0] == "git":
                return ieantn.subprocess.CompletedProcess(
                    args, 0, "https://github.com/teorth/IEANTN.git\n", "")
            target = args[2]
            calls.append(target)
            if target.endswith("/jobs"):
                return ieantn.subprocess.CompletedProcess(
                    args, 0, "\n".join(job_names), "")
            return ieantn.subprocess.CompletedProcess(
                args, 0, f"{conclusion}\t.github/workflows/verify.yml\n", "")

        return response, calls

    def verdict(self, job_names: list[str]) -> tuple[bool, str, list[str]]:
        response, calls = self.answered_by(job_names)
        printed = io.StringIO()
        with unittest.mock.patch.object(ieantn.subprocess, "run", side_effect=response), \
                contextlib.redirect_stdout(printed):
            passed = ieantn.check_receipts(online=True)
        return passed, printed.getvalue(), calls


class TestOneRunSeveralNodes(BatchedReceipts):
    def test_a_batched_run_is_accepted_when_its_job_names_name_each_node(self) -> None:
        """The case the old rule rejected. Both nodes appear in the run's job names, so the
        binding holds for each receipt separately and there is nothing left to object to."""
        self.receipt("A.v1.main")
        self.receipt("B.v1.main")
        passed, output, _ = self.verdict([
            "Plan",
            "Approve this verification",
            "Run Comparator (A.v1)",
            "Run Comparator (B.v1)",
            "Record the receipt (A.v1)",
            "Record the receipt (B.v1)",
        ])
        self.assertTrue(passed, output)

    def test_a_batched_run_must_still_name_every_node_that_cites_it(self) -> None:
        """The forgery, now that uniqueness alone no longer catches it: a receipt for a node the
        run never verified, citing a run that really did verify something."""
        self.receipt("A.v1.main")
        self.receipt("Forged.v9.main")
        passed, output, _ = self.verdict([
            "Run Comparator (A.v1)",
            "Record the receipt (A.v1)",
        ])
        self.assertFalse(passed)
        self.assertIn("Forged.v9", output)

    def test_a_run_from_before_the_convention_still_covers_one_node(self) -> None:
        """No parenthesised job name means no per-node record, so the older rule is all there is
        and it still applies. Such runs cannot be re-run, which is why they are tolerated at all."""
        self.receipt("A.v1.main")
        self.receipt("B.v1.main")
        passed, output, _ = self.verdict(["comparator", "receipt"])
        self.assertFalse(passed)
        self.assertIn("before the job-name convention", output)

    def test_one_node_citing_a_legacy_run_is_still_fine(self) -> None:
        self.receipt("A.v1.main")
        passed, output, _ = self.verdict(["comparator", "receipt"])
        self.assertTrue(passed, output)

    def test_two_receipts_of_the_same_node_are_not_a_collision(self) -> None:
        """A node with two conclusions is verified all at once, so its receipts share a run."""
        self.receipt("A.v1.first")
        self.receipt("A.v1.second")
        passed, output, _ = self.verdict(["comparator", "receipt"])
        self.assertTrue(passed, output)

    def test_an_unsuccessful_run_is_refused_however_it_is_named(self) -> None:
        self.receipt("A.v1.main")
        response, _ = self.answered_by(["Run Comparator (A.v1)"], conclusion="failure")
        printed = io.StringIO()
        with unittest.mock.patch.object(ieantn.subprocess, "run", side_effect=response), \
                contextlib.redirect_stdout(printed):
            self.assertFalse(ieantn.check_receipts(online=True))
        self.assertIn("not `success`", printed.getvalue())


class TestRunIsAskedAboutOnce(BatchedReceipts):
    """A batched run has several receipts, and asking GitHub once per receipt multiplies the
    chance of the 5xx that failed this check once already."""

    def test_three_receipts_on_one_run_ask_twice_not_six_times(self) -> None:
        for conclusion in ("A.v1.main", "B.v1.main", "C.v1.main"):
            self.receipt(conclusion)
        passed, output, calls = self.verdict([
            "Run Comparator (A.v1)", "Run Comparator (B.v1)", "Run Comparator (C.v1)"])
        self.assertTrue(passed, output)
        self.assertEqual(len(calls), 2, f"asked GitHub {len(calls)} times: {calls}")

    def test_distinct_runs_are_each_asked_about(self) -> None:
        self.receipt("A.v1.main", RUN)
        self.receipt("B.v1.main", OTHER_RUN)
        _, _, calls = self.verdict(["Run Comparator (A.v1)", "Run Comparator (B.v1)"])
        self.assertEqual(len(calls), 4, calls)


if __name__ == "__main__":
    unittest.main()
