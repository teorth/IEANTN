"""Fork report targets come from the trusted run commit, not artifact data."""
import contextlib
import io
import json
import pathlib
import tempfile
import unittest
from unittest import mock

from test_review_report import HEAD, OTHER, fork_event, payload, review_report

REPO = "example/project"
ASSOCIATED = f"/repos/{REPO}/commits/{HEAD}/pulls?per_page=100"


def pull(number=7, state="open", sha=HEAD):
    return {
        "number": number, "state": state,
        "head": {"sha": sha, "ref": "topic", "repo": {"full_name": "contributor/ieantn"}},
        "base": {"repo": {"full_name": REPO}},
    }


class TestForkReviewContext(unittest.TestCase):
    def post(self, event, responses, report=None):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "review-report.json"
            path.write_text(json.dumps(payload() if report is None else report), encoding="utf-8")
            with mock.patch.object(review_report, "_api", side_effect=responses) as api, \
                 contextlib.redirect_stdout(io.StringIO()):
                result = review_report.post_review(event, path, REPO, "fixture-token")
        return result, api

    def test_empty_fork_array_resolves_and_posts_to_commit_association(self):
        result, api = self.post(fork_event(), [
            ([pull()], ""), (pull(), ""), ([], ""), ({"id": 11}, ""),
        ])
        self.assertEqual(result, 0)
        self.assertEqual(api.call_args_list[0], mock.call("GET", ASSOCIATED, None, "fixture-token"))
        self.assertEqual(api.call_args_list[1].args[1], f"/repos/{REPO}/pulls/7")
        method, path, body, token = api.call_args_list[-1].args
        self.assertEqual((method, path, token), ("POST", f"/repos/{REPO}/issues/7/comments", "fixture-token"))
        self.assertTrue(body["body"].startswith(review_report.MARKER + "\n"))
        self.assertIn(HEAD, body["body"])

    def test_event_pull_number_is_not_used_as_a_shortcut(self):
        event = fork_event()
        event["workflow_run"]["pull_requests"] = [{"number": 7}]
        _, api = self.post(event, [([pull()], ""), (pull(), ""), ([], ""), ({}, "")])
        self.assertEqual(api.call_args_list[0].args[1], ASSOCIATED)
        self.assertEqual(api.call_args_list[-1].args[1], f"/repos/{REPO}/issues/7/comments")

    def test_artifact_sha_cannot_choose_the_comment_target(self):
        _, api = self.post(fork_event(), [
            ([pull()], ""), (pull(), ""), ([], ""), ({}, ""),
        ], payload(head_sha=OTHER))
        self.assertEqual(api.call_args_list[0].args[1], ASSOCIATED)
        body = api.call_args_list[-1].args[2]["body"]
        self.assertIn(f"Bound to head `{HEAD}`", body)
        self.assertIn("which is not the head SHA", body)
        self.assertIn(OTHER, body)

    def test_paginated_lookup_does_not_stop_at_an_empty_page(self):
        next_path = ASSOCIATED + "&page=2"
        result, api = self.post(fork_event(), [
            ([], f'<https://api.github.com{next_path}>; rel="next"'),
            ([pull()], ""), (pull(), ""), ([], ""), ({}, ""),
        ])
        self.assertEqual(result, 0)
        self.assertEqual(api.call_args_list[1].args[1], next_path)
        self.assertEqual(api.call_args_list[-1].args[1], f"/repos/{REPO}/issues/7/comments")

    def test_closed_origin_does_not_redirect_analysis_to_another_base(self):
        closed = pull(7, "closed")
        closed["base"]["ref"] = "main"
        other = pull(42)
        other["base"]["ref"] = "release"
        for supplied_origin in (False, True):
            event = fork_event()
            if supplied_origin:
                event["workflow_run"]["pull_requests"] = [{"number": 7}]
            with self.subTest(supplied_origin=supplied_origin), \
                 mock.patch.object(review_report, "load_report_file") as load, \
                 mock.patch.object(review_report, "_api", return_value=([closed, other], "")) as api:
                with self.assertRaisesRegex(review_report.ReviewReportError, "ambiguous"):
                    review_report.post_review(event, pathlib.Path("unused"), REPO, "fixture-token")
                load.assert_not_called()
                self.assertEqual([call.args[0] for call in api.call_args_list], ["GET"])

    def test_trusted_origin_is_not_replaced_by_another_unique_open_match(self):
        event = fork_event()
        event["workflow_run"]["pull_requests"] = [{"number": 7}]
        with mock.patch.object(review_report, "_api", return_value=([pull(42)], "")) as api:
            with self.assertRaisesRegex(review_report.ReviewReportError, "trusted event"):
                review_report.post_review(event, pathlib.Path("unused"), REPO, "fixture-token")
        api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_report_workflow_serializes_lookup_and_create(self):
        import yaml
        workflow = pathlib.Path(__file__).resolve().parents[1] / ".github/workflows/review-report.yml"
        document = yaml.safe_load(workflow.read_text(encoding="utf-8"))
        resolver = document["jobs"]["resolve"]
        commenter = document["jobs"]["comment"]
        self.assertEqual(resolver["permissions"]["pull-requests"], "read")
        self.assertNotIn("write", resolver["permissions"].values())
        self.assertEqual(commenter["needs"], "resolve")
        self.assertEqual(commenter["concurrency"]["group"],
                         "ieantn-review-report-${{ needs.resolve.outputs.pull_request }}")
        self.assertIs(commenter["concurrency"]["cancel-in-progress"], False)
        for job in (resolver, commenter):
            checkout = job["steps"][0]["with"]
            self.assertEqual(checkout["ref"], "${{ github.sha }}")
            self.assertIs(checkout["persist-credentials"], False)
        post = commenter["steps"][-1]
        self.assertEqual(post["env"]["EXPECTED_PR"], "${{ needs.resolve.outputs.pull_request }}")
        self.assertIn('--expected-pr "$EXPECTED_PR"', post["run"])

    def test_two_open_matches_on_different_pages_refuse_before_artifact_read(self):
        next_path = ASSOCIATED + "&page=2"
        with mock.patch.object(review_report, "load_report_file") as load, \
             mock.patch.object(review_report, "_api", side_effect=[
                 ([pull()], f'<https://api.github.com{next_path}>; rel="next"'),
                 ([pull(8)], ""),
             ]) as api:
            with self.assertRaisesRegex(review_report.ReviewReportError, "more than one"):
                review_report.post_review(fork_event(), pathlib.Path("unused"), REPO, "fixture-token")
        load.assert_not_called()
        self.assertEqual([call.args[0] for call in api.call_args_list], ["GET", "GET"])

    def test_no_open_match_does_not_read_artifact_or_write(self):
        with mock.patch.object(review_report, "load_report_file") as load, \
             mock.patch.object(review_report, "_api", return_value=([pull(state="closed")], "")) as api, \
             contextlib.redirect_stdout(io.StringIO()):
            result = review_report.post_review(fork_event(), pathlib.Path("unused"), REPO, "fixture-token")
        self.assertEqual(result, 0)
        load.assert_not_called()
        api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_invalid_association_identities_fail_closed(self):
        wrong_base = pull()
        wrong_base["base"]["repo"]["full_name"] = "other/project"
        for record in [pull(True), pull(0), pull("7"), wrong_base, "not an object"]:
            with self.subTest(record=record), \
                 mock.patch.object(review_report, "_api", return_value=([record], "")) as api:
                with self.assertRaises(review_report.ReviewReportError):
                    review_report._pull_request_number(REPO, HEAD, "fixture-token", "contributor/ieantn", "topic")
                self.assertEqual(api.call_args_list[0].args[0], "GET")

    def test_nonlist_association_response_fails_closed(self):
        with mock.patch.object(review_report, "_api", return_value=({"number": 7}, "")):
            with self.assertRaisesRegex(review_report.ReviewReportError, "not a list"):
                review_report._pull_request_number(REPO, HEAD, "fixture-token", "contributor/ieantn", "topic")

    def test_repeated_same_association_is_not_a_second_pull_request(self):
        with mock.patch.object(review_report, "_api", return_value=([pull(), pull()], "")):
            self.assertEqual(review_report._pull_request_number(REPO, HEAD, "fixture-token", "contributor/ieantn", "topic"), 7)

    def test_closed_between_lookup_and_post_is_not_commented_on(self):
        result, api = self.post(fork_event(), [([pull()], ""), (pull(state="closed"), "")])
        self.assertEqual(result, 0)
        self.assertEqual([call.args[0] for call in api.call_args_list], ["GET", "GET"])

    def test_stale_run_still_reports_the_trusted_original_sha(self):
        _, api = self.post(fork_event(), [
            ([pull(sha=OTHER)], ""), (pull(sha=OTHER), ""), ([], ""), ({}, ""),
        ])
        body = api.call_args_list[-1].args[2]["body"]
        self.assertIn("**Stale.**", body)
        self.assertIn(f"Bound to head `{HEAD}`", body)
        self.assertIn(f"head is now `{OTHER}`", body)

    def test_existing_marker_comment_is_updated_not_duplicated(self):
        _, api = self.post(fork_event(), [
            ([pull()], ""), (pull(), ""),
            ([{"id": 13, "body": review_report.MARKER + "\nold report"}], ""), ({}, ""),
        ])
        self.assertEqual(api.call_args_list[-1].args[0:2],
                         ("PATCH", f"/repos/{REPO}/issues/comments/13"))

    def test_invalid_or_unsuccessful_run_never_contacts_api(self):
        events = [None, {}, {"workflow_run": []}]
        for key, value in [("head_sha", "../invalid"), ("head_sha", True),
                           ("conclusion", "failure"), ("event", "push")]:
            event = fork_event()
            event["workflow_run"][key] = value
            events.append(event)
        for event in events:
            with self.subTest(event=event), mock.patch.object(review_report, "_api") as api, \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(review_report.post_review(event, pathlib.Path("unused"), REPO, "fixture-token"), 0)
                api.assert_not_called()

    def test_api_failure_is_not_retried_or_followed_by_a_write(self):
        with mock.patch.object(review_report, "_api", side_effect=review_report.ReviewReportError("denied")) as api:
            with self.assertRaisesRegex(review_report.ReviewReportError, "denied"):
                review_report.post_review(fork_event(), pathlib.Path("unused"), REPO, "fixture-token")
        api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_all_finding_mentions_are_neutralized(self):
        text = "@fixture-user\ninline @fixture-org/team and `@fixture-user`"
        report = payload(findings=[{"level": "informational", "body": text}])
        body = review_report.render_review_report(report, {"run_head_sha": HEAD, "current_head_sha": HEAD})
        self.assertNotIn("@", body)
        self.assertIn("＠fixture-user", body)
        self.assertIn("＠fixture-org/team", body)
        self.assertTrue(body.startswith(review_report.MARKER + "\n"))
        self.assertLessEqual(len(body), review_report.MAX_COMMENT)
