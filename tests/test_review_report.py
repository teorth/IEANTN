"""The review comment is rendered from JSON and upserted by its marker.

No test here talks to GitHub. The comment list is a plain list of dicts.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

_PATH = pathlib.Path(__file__).resolve().parent.parent / "scripts" / "review_report.py"
_SPEC = importlib.util.spec_from_file_location("review_report", _PATH)
assert _SPEC and _SPEC.loader
review_report = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(review_report)

HEAD = "a" * 40
OTHER = "b" * 40


def payload(**overrides) -> dict:
    report = {
        "head_sha": HEAD,
        "findings": [{"level": "informational", "body": "new conclusion `A.v1.main` (`literature`)."}],
        "truncated": False,
    }
    report.update(overrides)
    return report


def fork_event() -> dict:
    return {
        "workflow_run": {
            "conclusion": "success",
            "event": "pull_request",
            "head_sha": HEAD,
            "head_repository": {"full_name": "contributor/ieantn"},
            "repository": {"full_name": "teorth/IEANTN"},
            "pull_requests": [{"number": 7}],
        }
    }


class TestReviewReport(unittest.TestCase):
    def test_fork_shaped_input_is_labelled_and_not_checked_out(self) -> None:
        trusted = review_report.trusted_run(fork_event())
        self.assertEqual(
            trusted, {"pull_request": 7, "run_head_sha": HEAD, "checkout_head": False}
        )
        self.assertNotIn("ref", trusted)
        pull = {
            "head": {"sha": HEAD, "repo": {"full_name": "contributor/ieantn"}},
            "base": {"repo": {"full_name": "teorth/IEANTN"}},
        }
        body = review_report.render_review_report(
            payload(), review_report.context_for(pull, HEAD)
        )
        self.assertTrue(body.startswith(review_report.MARKER + "\n"))
        self.assertIn("contributor/ieantn", body)
        self.assertIn("fork", body)
        self.assertIn(HEAD, body)
        self.assertNotIn("git checkout", body)
        self.assertNotIn("lake build", body)

    def test_stale_sha_is_called_out(self) -> None:
        context = {
            "current_head_sha": OTHER,
            "run_head_sha": HEAD,
            "head_repository": "teorth/IEANTN",
            "base_repository": "teorth/IEANTN",
        }
        body = review_report.render_review_report(payload(), context)
        self.assertIn("**Stale.**", body)
        self.assertIn(HEAD, body)
        self.assertIn(OTHER, body)
        self.assertIn("pull request head is now", body)

    def test_truncation_is_reported(self) -> None:
        findings = [
            {"level": "informational", "body": f"note {index}"} for index in range(review_report.MAX_FINDINGS + 1)
        ]
        body = review_report.render_review_report(
            payload(findings=findings, truncated=False),
            {"current_head_sha": HEAD, "run_head_sha": HEAD,
             "head_repository": "teorth/IEANTN", "base_repository": "teorth/IEANTN"},
        )
        self.assertIn("Findings were truncated.", body)
        self.assertNotIn(f"note {review_report.MAX_FINDINGS}", body)
        self.assertIn("note 0", body)
        flagged = review_report.render_review_report(
            payload(truncated=True),
            {"current_head_sha": HEAD, "run_head_sha": HEAD,
             "head_repository": "teorth/IEANTN", "base_repository": "teorth/IEANTN"},
        )
        self.assertIn("Findings were truncated.", flagged)

    def test_rerun_updates_the_same_marker_comment(self) -> None:
        context = {
            "current_head_sha": HEAD,
            "run_head_sha": HEAD,
            "head_repository": "teorth/IEANTN",
            "base_repository": "teorth/IEANTN",
        }
        first = review_report.render_review_report(payload(), context)
        second = review_report.render_review_report(
            payload(findings=[{"level": "degraded", "body": "Receipt for `A.v1.main` is now **BROKEN**."}]),
            context,
        )
        self.assertNotEqual(first, second)
        comments = [
            {"id": 3, "body": "A review note that quotes the marker later\n" + review_report.MARKER},
            {"id": 11, "body": "unrelated"},
        ]
        created = review_report.upsert_review_comment(comments, first)
        self.assertEqual(created["action"], "create")
        self.assertNotIn("id", created)
        comments.append({"id": 8, "body": created["body"]})
        updated = review_report.upsert_review_comment(comments, second)
        self.assertEqual(updated, {"action": "update", "id": 8, "body": second})
        comments[-1]["body"] = updated["body"]
        again = review_report.upsert_review_comment(comments, first)
        self.assertEqual(again["action"], "update")
        self.assertEqual(again["id"], 8)
        self.assertEqual(
            [comment["id"] for comment in comments if review_report.comment_is_review_report(comment["body"])],
            [8],
        )


if __name__ == "__main__":
    unittest.main()
