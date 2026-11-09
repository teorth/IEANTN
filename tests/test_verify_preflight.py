"""Verification must cover the entire node before it spends a workflow run."""
import unittest.mock

from test_ieantn import FixtureRepo, LITERATURE, ieantn


class TestVerificationCoveragePreflight(FixtureRepo):
    def setUp(self):
        super().setUp()
        self.write_node("A.v1", LITERATURE + LITERATURE.replace("main", "second"))
        self.write_comparator_config("A.v1", ["A.v1.challenge_main"])

    def verify(self, *, precheck=True, local_head="tip"):
        calls = []

        def run(args, **kwargs):
            calls.append(args)
            output = ("https://github.com/teorth/IEANTN/actions/runs/42\n"
                      if args[:3] == ["gh", "workflow", "run"] else local_head + "\n")
            return ieantn.subprocess.CompletedProcess(args, 0, output, "")

        def gh(args):
            return "42" if args[0] == "run" else "completed\tsuccess"

        with unittest.mock.patch.object(ieantn, "repository_slug", return_value="teorth/IEANTN"), \
             unittest.mock.patch.object(ieantn, "remote_branch_sha", return_value="tip"), \
             unittest.mock.patch.object(ieantn, "solution_holes", return_value=(True, [], {
                 "A.v1.challenge_main": True,
             })) as probe, \
             unittest.mock.patch.object(ieantn.subprocess, "run", side_effect=run), \
             unittest.mock.patch.object(ieantn, "_gh_json", side_effect=gh), \
             unittest.mock.patch.object(ieantn.time, "sleep"):
            result = ieantn.verify("A.v1", "contribution", dispatch=True, precheck=precheck)
        dispatches = [args for args in calls if args[:3] == ["gh", "workflow", "run"]]
        return result, dispatches, probe.call_count

    def test_a_proved_subset_does_not_dispatch_an_unreceiptable_node(self):
        self.assertEqual(self.verify(), (False, [], 0))

    def test_empty_comparator_does_not_dispatch(self):
        self.write_comparator_config("A.v1", [])
        self.assertEqual(self.verify(), (False, [], 0))

    def test_malformed_comparator_is_reported_before_building(self):
        (self.root / "Solutions/A.v1/comparator.json").write_text("{")
        self.assertEqual(self.verify(), (False, [], 0))

    def test_complete_coverage_reaches_the_proof_probe_and_dispatch(self):
        self.write_comparator_config("A.v1", ["A.v1.challenge_main", "A.v1.challenge_second"])
        result, dispatches, probes = self.verify()
        self.assertTrue(result)
        self.assertEqual(len(dispatches), 1)
        self.assertEqual(probes, 1)

    def test_explicit_skip_and_a_different_remote_tree_keep_their_behavior(self):
        for options in ({"precheck": False}, {"local_head": "other"}):
            with self.subTest(options=options):
                result, dispatches, probes = self.verify(**options)
                self.assertTrue(result)
                self.assertEqual(len(dispatches), 1)
                self.assertEqual(probes, 0)
