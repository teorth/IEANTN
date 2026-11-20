"""Progress probes must be read-only and must succeed before progress can be recorded."""
import json
import unittest.mock
from test_ieantn import FixtureRepo, ieantn


class TestProgressProbe(FixtureRepo):
    def setup_solution(self):
        directory = self.root / "Solutions" / "A.v1"
        directory.mkdir(parents=True)
        (directory / "lakefile.toml").write_text('name = "fixture"\n')
        (directory / "comparator.json").write_text(json.dumps({
            "solution_module": "Proof", "theorem_names": ["A.v1.challenge_main"]}))
        (directory / "Proof.lean").write_text("-- proof fixture\n")
        return directory

    def run_probe(self, directory, fail=False):
        observed = []
        def run(args, **kwargs):
            if args[:3] == ["lake", "env", "lean"]:
                text = (directory / args[3]).read_text()
                if "#print axioms" in text:
                    observed.append(text)
                    return ieantn.subprocess.CompletedProcess(args, int(fail),
                        "'A.v1.challenge_main' depends on axioms: [propext]\n", "")
            return ieantn.subprocess.CompletedProcess(args, 0, "", "")
        with unittest.mock.patch.object(ieantn.subprocess, "run", side_effect=run):
            result = ieantn.solution_holes("A.v1")
        return result, observed

    def test_existing_scratch_file_survives_and_configured_module_is_used(self):
        directory = self.setup_solution()
        scratch = directory / "_ieantn_axioms.lean"
        scratch.write_text("-- contributor scratch work\n")
        before = set(directory.iterdir())
        result, observed = self.run_probe(directory)
        self.assertEqual(scratch.read_text(), "-- contributor scratch work\n")
        self.assertEqual(set(directory.iterdir()), before)
        self.assertEqual(result, (True, [], {"A.v1.challenge_main": True}))
        self.assertTrue(observed[0].startswith("import Proof\n"))

    def test_failed_probe_cannot_report_partial_output_as_proved(self):
        directory = self.setup_solution()
        before = set(directory.iterdir())
        result, _ = self.run_probe(directory, fail=True)
        self.assertEqual(result, (False, [], {}))
        self.assertEqual(set(directory.iterdir()), before)

    def test_nested_holes_keep_their_distinct_relative_locations(self):
        directory = self.setup_solution()
        for parent in ("First", "Second"):
            source = directory / parent / "Lemmas.lean"
            source.parent.mkdir()
            source.write_text("theorem unfinished : True := by sorry\n")
        # Installed dependencies and build products are not part of this solution.
        dependency = directory / ".lake" / "packages" / "library" / "Broken.lean"
        dependency.parent.mkdir(parents=True)
        dependency.write_text("not valid Lean\n")
        checked_sources = []

        def run(args, **kwargs):
            output = ""
            if args[:3] == ["lake", "env", "lean"]:
                source = args[3]
                checked_sources.append(source)
                if source.startswith("_ieantn_axioms_"):
                    output = "'A.v1.challenge_main' does not depend on any axioms\n"
                elif source in ("First/Lemmas.lean", "Second/Lemmas.lean"):
                    output = f"{source}:1:0: warning: declaration uses 'sorry'\n"
                elif source != "Proof.lean":
                    return ieantn.subprocess.CompletedProcess(args, 1, "", "bad dependency")
            return ieantn.subprocess.CompletedProcess(args, 0, output, "")

        with unittest.mock.patch.object(ieantn.subprocess, "run", side_effect=run):
            result = ieantn.solution_holes("A.v1")
        self.assertEqual(result, (True, ["First/Lemmas.lean:1", "Second/Lemmas.lean:1"],
                                  {"A.v1.challenge_main": True}))
        self.assertIn("First/Lemmas.lean", checked_sources)
        self.assertIn("Second/Lemmas.lean", checked_sources)
        self.assertFalse(any(".lake" in source for source in checked_sources))

    def test_failed_nested_elaboration_cannot_report_zero_holes(self):
        directory = self.setup_solution()
        source = directory / "Proofs" / "Aux.lean"
        source.parent.mkdir()
        source.write_text("-- imported build product can already exist\n")

        def run(args, **kwargs):
            if args[:3] == ["lake", "env", "lean"] and args[3] == "Proofs/Aux.lean":
                return ieantn.subprocess.CompletedProcess(args, 1,
                    "Proofs/Aux.lean:1:0: error: elaboration failed\n", "")
            return ieantn.subprocess.CompletedProcess(args, 0, "", "")

        with unittest.mock.patch.object(ieantn.subprocess, "run", side_effect=run):
            result = ieantn.solution_holes("A.v1")
        self.assertEqual(result, (False, [], {}))
