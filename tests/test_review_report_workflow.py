"""Read-only discovery binds the later per-PR comment job to its resolved target."""
import contextlib
import io
import json
import os
import pathlib
import tempfile
import unittest
from unittest import mock

from test_review_report import HEAD, fork_event, payload, review_report
from test_review_report_fork_context import ASSOCIATED, REPO, pull


class TestReviewWorkflowTarget(unittest.TestCase):
    def test_other_fork_or_branch_cannot_receive_the_report(self):
        for wrong_repo, wrong_branch in [(True, False), (False, True), (True, True)]:
            candidate = pull(42)
            if wrong_repo:
                candidate["head"]["repo"]["full_name"] = "other-fork/project"
            if wrong_branch:
                candidate["head"]["ref"] = "other-topic"
            with self.subTest(wrong_repo=wrong_repo, wrong_branch=wrong_branch), \
                 mock.patch.object(review_report, "_api", return_value=([candidate], "")) as api, \
                 mock.patch.object(review_report, "load_report_file") as load, \
                 contextlib.redirect_stdout(io.StringIO()):
                result = review_report.post_review(fork_event(), pathlib.Path("unused"), REPO, "fixture-token")
                self.assertEqual(result, 0)
                load.assert_not_called()
                api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_source_is_rechecked_after_lookup(self):
        renamed = pull()
        renamed["head"]["ref"] = "renamed-topic"
        with mock.patch.object(review_report, "_api", side_effect=[([pull()], ""), (renamed, "")]) as api, \
             mock.patch.object(review_report, "load_report_file", return_value=payload()):
            with self.assertRaisesRegex(review_report.ReviewReportError, "source no longer matches"):
                review_report.post_review(fork_event(), pathlib.Path("unused"), REPO, "fixture-token")
        self.assertEqual([call.args[0] for call in api.call_args_list], ["GET", "GET"])

    def test_target_change_cannot_escape_the_acquired_pr_lock(self):
        with mock.patch.object(review_report, "_api", return_value=([pull(42)], "")) as api, \
             mock.patch.object(review_report, "load_report_file") as load:
            with self.assertRaisesRegex(review_report.ReviewReportError, "comment lock"):
                review_report.post_review(fork_event(), pathlib.Path("unused"), REPO,
                                          "fixture-token", expected_number=7)
        load.assert_not_called()
        api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_resolve_cli_outputs_only_a_numeric_target_and_never_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            event = pathlib.Path(directory) / "event.json"
            event.write_text(json.dumps(fork_event()), encoding="utf-8")
            for matches, expected in [([pull()], "pull_request=7\n"), ([], "pull_request=\n")]:
                output = io.StringIO()
                with self.subTest(matches=matches), \
                     mock.patch.dict(os.environ, {"GH_TOKEN": "fixture-token"}, clear=True), \
                     mock.patch.object(review_report, "_api", return_value=(matches, "")) as api, \
                     contextlib.redirect_stdout(output):
                    self.assertEqual(review_report.main([
                        "resolve", "--event", str(event), "--repo", REPO,
                    ]), 0)
                self.assertEqual(output.getvalue(), expected)
                api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_missing_or_malformed_source_identity_never_contacts_api(self):
        for key, value in [("head_branch", ""), ("head_branch", None),
                           ("head_repository", {}), ("head_repository", {"full_name": "not/a/repo"})]:
            event = fork_event()
            event["workflow_run"][key] = value
            with self.subTest(key=key, value=value), mock.patch.object(review_report, "_api") as api:
                self.assertIsNone(review_report.resolve_review_target(event, REPO, "fixture-token"))
                api.assert_not_called()

    def test_explicit_pr_number_does_not_attest_the_original_analysis_base(self):
        event = fork_event()
        event["workflow_run"]["pull_requests"] = [
            {"number": 7, "base": {"ref": "main", "sha": "c" * 40}},
        ]
        retargeted = pull()
        retargeted["base"].update({"ref": "release", "sha": "d" * 40})
        with mock.patch.object(review_report, "_api", side_effect=[
            ([retargeted], ""), (retargeted, ""), ([], ""), ({}, ""),
        ]) as api, mock.patch.object(review_report, "load_report_file", return_value=payload(findings=[])), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(review_report.post_review(
                event, pathlib.Path("unused"), REPO, "fixture-token", expected_number=7,
            ), 0)
        body = api.call_args_list[-1].args[2]["body"]
        self.assertIn("original base is not independently attested", body)
        self.assertIn("Base-relative findings are not confirmed", body)
        self.assertNotIn("did not identify its originating pull request", body)

    def test_empty_event_does_not_attest_the_original_analysis_base(self):
        output = io.StringIO()
        with mock.patch.object(review_report, "_api", side_effect=[
            ([pull()], ""), (pull(), ""), ([], ""), ({}, ""),
        ]) as api, mock.patch.object(review_report, "load_report_file", return_value=payload()), \
             contextlib.redirect_stdout(output):
            self.assertEqual(review_report.post_review(
                fork_event(), pathlib.Path("unused"), REPO, "fixture-token", expected_number=7,
            ), 0)
        body = api.call_args_list[-1].args[2]["body"]
        self.assertIn("original base is not independently attested", body)
        self.assertIn("Base-relative findings are not confirmed", body)
        self.assertIn(f"Bound to head `{HEAD}`", body)
        self.assertEqual(api.call_args_list[-1].args[1], f"/repos/{REPO}/issues/7/comments")
