"""Empty base-repository associations fall back to the trusted fork, never artifact data."""
import contextlib
import io
import pathlib
import unittest
from unittest import mock

from test_review_report import HEAD, OTHER, fork_event, payload, review_report
from test_review_report_fork_context import ASSOCIATED, REPO, pull

FORK_ASSOCIATED = f"/repos/contributor/ieantn/commits/{HEAD}/pulls?per_page=100"


class TestForkRepositoryFallback(unittest.TestCase):
    def test_live_empty_base_response_resolves_the_trusted_fork(self):
        sha = "8af9d0c2911ef44e5afdeee28f5fa62d18ea57de"
        event = fork_event()
        event["workflow_run"].update(
            head_sha=sha, head_branch="codex/pr-review-report",
            head_repository={"full_name": "chessing234/IEANTN"},
        )
        candidate = pull(221, sha=sha)
        candidate["head"].update(ref="codex/pr-review-report", repo={"full_name": "chessing234/IEANTN"})
        candidate["base"]["repo"]["full_name"] = "teorth/IEANTN"
        with mock.patch.object(review_report, "_api", side_effect=[([], ""), ([candidate], "")]) as api:
            target = review_report.resolve_review_target(event, "teorth/IEANTN", "fixture-token")
        self.assertEqual(target[1], 221)
        self.assertEqual(api.call_args_list, [
            mock.call("GET", f"/repos/teorth/IEANTN/commits/{sha}/pulls?per_page=100", None, "fixture-token"),
            mock.call("GET", f"/repos/chessing234/IEANTN/commits/{sha}/pulls?per_page=100", None, "fixture-token"),
        ])

    def test_fallback_post_keeps_trusted_sha_source_recheck_and_base_caveat(self):
        with mock.patch.object(review_report, "_api", side_effect=[
            ([], ""), ([pull()], ""), (pull(), ""), ([], ""), ({"id": 11}, ""),
        ]) as api, mock.patch.object(review_report, "load_report_file", return_value=payload(head_sha=OTHER)), \
             contextlib.redirect_stdout(io.StringIO()):
            result = review_report.post_review(
                fork_event(), pathlib.Path("unused"), REPO, "fixture-token", expected_number=7,
            )
        self.assertEqual(result, 0)
        self.assertEqual(api.call_args_list[0].args[1], ASSOCIATED)
        self.assertEqual(api.call_args_list[1].args[1], FORK_ASSOCIATED)
        self.assertEqual(api.call_args_list[2].args[1], f"/repos/{REPO}/pulls/7")
        method, path, body, _token = api.call_args_list[-1].args
        self.assertEqual((method, path), ("POST", f"/repos/{REPO}/issues/7/comments"))
        self.assertIn(f"Bound to head `{HEAD}`", body["body"])
        self.assertIn("original base is not independently attested", body["body"])
        self.assertIn("Base-relative findings are not confirmed", body["body"])

    def test_fallback_filters_associations_to_the_destination_repository(self):
        unrelated = pull(42)
        unrelated["base"]["repo"]["full_name"] = "another/project"
        with mock.patch.object(review_report, "_api", side_effect=[
            ([], ""), ([unrelated, pull()], ""),
        ]):
            self.assertEqual(review_report.resolve_review_target(fork_event(), REPO, "fixture-token")[1], 7)

    def test_fallback_paginates_and_deduplicates(self):
        next_path = FORK_ASSOCIATED + "&page=2"
        with mock.patch.object(review_report, "_api", side_effect=[
            ([], ""), ([pull()], f'<https://api.github.com{next_path}>; rel="next"'),
            ([pull()], ""),
        ]) as api:
            self.assertEqual(review_report.resolve_review_target(fork_event(), REPO, "fixture-token")[1], 7)
        self.assertEqual(api.call_args_list[-1].args[1], next_path)
        self.assertTrue(all(call.args[0] == "GET" for call in api.call_args_list))

    def test_fallback_refuses_ambiguity_including_closed_associations(self):
        for other in (pull(8), pull(8, "closed")):
            with self.subTest(other=other), mock.patch.object(review_report, "_api", side_effect=[
                ([], ""), ([pull(), other], ""),
            ]), mock.patch.object(review_report, "load_report_file") as load:
                with self.assertRaises(review_report.ReviewReportError):
                    review_report.post_review(fork_event(), pathlib.Path("unused"), REPO, "fixture-token")
                load.assert_not_called()

    def test_fallback_must_agree_with_trusted_event_identity(self):
        event = fork_event()
        event["workflow_run"]["pull_requests"] = [{"number": 42}]
        with mock.patch.object(review_report, "_api", side_effect=[([], ""), ([pull()], "")]):
            with self.assertRaisesRegex(review_report.ReviewReportError, "trusted event"):
                review_report.resolve_review_target(event, REPO, "fixture-token")

    def test_fallback_must_still_match_the_run_fork_and_branch(self):
        for field, value in (("ref", "other-topic"), ("repo", {"full_name": "another/fork"})):
            candidate = pull()
            candidate["head"][field] = value
            with self.subTest(field=field), mock.patch.object(review_report, "_api", side_effect=[
                ([], ""), ([candidate], ""),
            ]):
                self.assertIsNone(review_report.resolve_review_target(fork_event(), REPO, "fixture-token"))

    def test_nonempty_base_associations_do_not_redirect_through_the_fork(self):
        with mock.patch.object(review_report, "_api", return_value=([pull(state="closed")], "")) as api:
            self.assertIsNone(review_report.resolve_review_target(fork_event(), REPO, "fixture-token"))
        api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_same_repository_run_does_not_repeat_an_empty_lookup(self):
        event = fork_event()
        event["workflow_run"]["head_repository"]["full_name"] = REPO
        with mock.patch.object(review_report, "_api", return_value=([], "")) as api:
            self.assertIsNone(review_report.resolve_review_target(event, REPO, "fixture-token"))
        api.assert_called_once_with("GET", ASSOCIATED, None, "fixture-token")

    def test_malformed_or_failed_fallback_fails_before_artifact_read(self):
        invalid = pull()
        invalid["base"]["repo"] = {}
        for response in (({"number": 7}, ""), ([invalid], ""), review_report.ReviewReportError("unavailable")):
            with self.subTest(response=response), mock.patch.object(review_report, "_api", side_effect=[
                ([], ""), response,
            ]) as api, mock.patch.object(review_report, "load_report_file") as load:
                with self.assertRaises(review_report.ReviewReportError):
                    review_report.post_review(fork_event(), pathlib.Path("unused"), REPO, "fixture-token")
                load.assert_not_called()
                self.assertEqual([call.args[0] for call in api.call_args_list], ["GET", "GET"])


if __name__ == "__main__":
    unittest.main()
