"""A dispatch must follow its own run even if another verification starts later."""
import unittest.mock

from test_ieantn import FixtureRepo, ieantn


class TestDispatchedRunIdentity(FixtureRepo):
    def dispatch(self, output):
        requests = []

        def gh(args):
            requests.append(args)
            return "222" if args[0] == "run" else "completed\tsuccess"

        with unittest.mock.patch.object(ieantn, "repository_slug", return_value="teorth/IEANTN"), \
             unittest.mock.patch.object(ieantn, "remote_branch_sha", return_value="tip"), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=
                 ieantn.subprocess.CompletedProcess([], 0, output, "")), \
             unittest.mock.patch.object(ieantn, "_gh_json", side_effect=gh), \
             unittest.mock.patch.object(ieantn.time, "sleep"):
            result = ieantn.verify("A.v1", "contribution", dispatch=True, precheck=False)
        return result, requests

    def test_newer_unrelated_run_cannot_replace_the_dispatched_run(self):
        result, requests = self.dispatch("https://github.com/teorth/IEANTN/actions/runs/111\n")
        self.assertTrue(result)
        self.assertFalse(any(args[0] == "run" for args in requests))
        self.assertEqual(requests[0][1], "repos/teorth/IEANTN/actions/runs/111")

    def test_missing_run_url_does_not_report_an_existing_success(self):
        self.assertEqual(self.dispatch("Created workflow_dispatch event\n"), (False, []))

    def test_a_url_from_another_repository_is_not_accepted(self):
        self.assertEqual(self.dispatch("https://github.com/other/project/actions/runs/111\n"),
                         (False, []))
