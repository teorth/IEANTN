"""A failed Git read is not an empty network baseline."""
import contextlib
import io
import shutil
import subprocess
from test_ieantn import LITERATURE, REFUTED, FixtureRepo, bridged, ieantn, importing


class _DiffGit(FixtureRepo):
    def git(self, *args):
        return subprocess.run(
            ["git", "-c", "commit.gpgsign=false", *args],
            cwd=self.root, check=True, capture_output=True, text=True,
        )

    def setUp(self):
        super().setUp()
        self.git("init", "-q")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--allow-empty", "-m", "Empty base")

    def commit_all(self, message: str) -> None:
        self.git("add", "-A")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "-q", "-m", message)

    def report(self) -> str:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            result = ieantn.diff("HEAD")
        output.seek(0)
        text = output.getvalue()
        self._last_ok = result
        return text


class TestDiffBase(_DiffGit):
    def test_unknown_base_does_not_report_all_conclusions_as_new(self):
        self.write_node("A.v1", LITERATURE)
        output = io.StringIO()
        with contextlib.redirect_stdout(output), self.assertRaisesRegex(SystemExit, "cannot read network base"):
            ieantn.diff("missing-base")
        self.assertNotIn("new conclusion", output.getvalue())

    def test_valid_empty_base_is_still_supported(self):
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.diff("HEAD"))
        self.assertEqual(ieantn.state_at("HEAD")["conclusions"], {})


class TestRemovedConclusions(_DiffGit):
    def test_removal_allows_importers_migrated_in_the_same_change(self):
        old = self.write_node("A.v1", LITERATURE)
        self.write_node("A.v2", LITERATURE)
        self.write_node("B.v1", importing("A.v1"))
        self.commit_all("base")
        self.write_node("B.v1", importing("A.v2"))
        shutil.rmtree(old)

        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertIn("`A.v1.main` removed; nothing imported it.", text)
        self.assertNotIn("### Breaking", text)

    def test_removal_still_fails_when_a_new_importer_replaces_a_migrated_one(self):
        old = self.write_node("A.v1", LITERATURE)
        self.write_node("A.v2", LITERATURE)
        self.write_node("B.v1", importing("A.v1"))
        self.commit_all("base")
        self.write_node("B.v1", importing("A.v2"))
        self.write_node("C.v1", importing("A.v1"))
        shutil.rmtree(old)

        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("`A.v1.main` was removed", text)
        self.assertIn("1 conclusion(s) still import it: `C.v1.main`.", text)
        self.assertNotIn("`B.v1.main`", text)

    def test_removal_still_fails_when_an_import_is_retained(self):
        old = self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", importing("A.v1"))
        self.commit_all("base")
        shutil.rmtree(old)

        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("`A.v1.main` was removed", text)
        self.assertIn("`B.v1.main`", text)


class TestBridgeLeafSet(_DiffGit):
    """A bridge may discharge assumptions. It may not acquire any.

    The leaf set is a property of the graph, so the check reads the committed yaml and the working
    tree and never asks Lean.
    """

    def test_a_bridge_that_acquires_an_assumption_fails(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        self.commit_all("base")
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Extra.v1"))
        self.write_node("A.v1", bridged("Mid.v1.main"))
        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("A.v1.main", text)
        self.assertIn("gained unproved assumptions", text)
        self.assertIn("Extra.v1.main", text)
        self.assertIn("Mid.v1.main", text)

    def test_an_acknowledgement_does_not_excuse_it(self) -> None:
        """The one `diff` error with no override, which is policy -- see docs/ROADMAP.md.

        Every other error is a conclusion edited in place, where a reviewer can weigh landing
        it against what it breaks. Here there is nothing to weigh: a restatement that rests on
        a new assumption is not a restatement, and the node should designate the weaker
        evidence it really has. An acknowledgement would record a bridge the network keeps
        trusting while knowing it transports less than it claims.
        """
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        self.commit_all("base")
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Extra.v1"))
        self.write_node("A.v1", bridged("Mid.v1.main"))
        changes = self.root / "changes"
        changes.mkdir()
        (changes / "bridge.yaml").write_text(
            "acknowledge:\n"
            "  - conclusion: A.v1.main\n"
            "    effect: receipt-voided\n"
            "    reason: >-\n"
            "      Acknowledging it must not help: this check has no override.\n",
            encoding="utf-8")
        # The acknowledgement is read -- an edit in place would be excused by it ...
        self.assertEqual(
            ieantn.acknowledged(),
            {"A.v1.main": "Acknowledging it must not help: this check has no override."})
        # ... and the leaf set still fails the branch.
        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("gained unproved assumptions", text)
        self.assertIn("does not cover", text)

    def test_discharging_an_assumption_is_a_note(self) -> None:
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Extra.v1"))
        self.write_node("A.v1", bridged("Mid.v1.main"))
        self.commit_all("base")
        self.write_node("A.v1", bridged("Extra.v1.main"))
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertIn("fewer unproved assumptions", text)
        self.assertIn("Mid.v1.main", text)
        self.assertNotIn("gained unproved assumptions", text)

    def test_an_unchanged_bridge_is_silent(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        self.commit_all("base")
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertNotIn("unproved assumptions", text)

    def test_a_new_bridged_conclusion_is_not_compared_to_nothing(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.commit_all("base")
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertIn("new conclusion `A.v1.main`", text)
        self.assertNotIn("gained unproved assumptions", text)

    def test_becoming_bridged_onto_a_new_leaf_fails(self) -> None:
        verified = LITERATURE.replace("kind: literature", "kind: lean-comparator")
        self.write_node("A.v1", verified)
        self.commit_all("base")
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("Leaf.v1.main", text)
        self.assertIn("gained unproved assumptions", text)

    def test_a_bridge_cycle_is_not_discharged_assumptions(self) -> None:
        """Closing the bridge onto itself used to empty the leaf set.

        `diff` then reported the lost citation as a bridge that rests on less, and the branch
        passed. The cycle is an unproved assumption, not a discharge.
        """
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", bridged("Leaf.v1.main"))
        self.commit_all("base")
        self.write_node("B.v1", bridged("A.v1.main"))
        self.write_node("A.v1", bridged("B.v1.main"))
        text = self.report()
        self.assertFalse(self._last_ok)
        self.assertIn("gained unproved assumptions", text)
        self.assertIn("A.v1.main", text)
        self.assertIn("B.v1.main", text)
        self.assertNotIn("fewer unproved assumptions", text)

    def test_an_unbridged_import_is_not_this_check(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("A.v1", importing("Leaf.v1"))
        self.commit_all("base")
        self.write_node("Extra.v1", LITERATURE)
        self.write_node("A.v1", importing("Extra.v1"))
        text = self.report()
        self.assertTrue(self._last_ok)
        self.assertNotIn("gained unproved assumptions", text)


class TestRefutationIsReported(_DiffGit):
    """Declaring a conclusion false is the strongest degradation there is, and the only one no
    other comparison here can see.

    Issues 260 and 268. A refutation leaves the statement untouched, so no fingerprint moves, and
    leaves the designated justification untouched too, so comparing kinds finds nothing. The first
    version of this reported "No change to any statement, dependency, or receipt." for a branch
    that had just declared two published lemmas false.
    """

    def test_a_new_refutation_is_degraded_not_silent(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.commit_all("A.v1 as published")
        self.write_node("A.v1", REFUTED)
        report = self.report()
        self.assertIn("### Degraded", report)
        self.assertIn("`A.v1.main` is now refuted", report)
        self.assertNotIn("No change to any statement", report)

    def test_it_names_the_consumers_that_want_rerouting(self) -> None:
        """`diff` exists to say what a branch degrades *and for whom*."""
        self.write_node("Upstream.v1", LITERATURE)
        self.write_node("Downstream.v1", importing("Upstream.v1"))
        self.generate()
        self.commit_all("both as published")
        self.write_node("Upstream.v1", REFUTED)
        report = self.report()
        self.assertIn("`Downstream.v1.main`", report)
        self.assertIn("rerouting", report)

    def test_a_refutation_does_not_fail_the_branch(self) -> None:
        """Recording a published result as false is a legitimate thing for a branch to do."""
        self.write_node("A.v1", LITERATURE)
        self.commit_all("A.v1 as published")
        self.write_node("A.v1", REFUTED)
        self.report()
        self.assertTrue(self._last_ok, "a refutation is reported, not refused")

    def test_withdrawing_a_refutation_is_informational(self) -> None:
        self.write_node("A.v1", REFUTED)
        self.commit_all("A.v1 refuted")
        self.write_node("A.v1", LITERATURE)
        report = self.report()
        self.assertIn("no longer refuted", report)
