"""The public evidence projection must preserve conditional trust, not just serialize YAML."""
import contextlib
import datetime
import io
import json
from unittest.mock import patch

from test_ieantn import FixtureRepo, LITERATURE, bridged_from, ieantn, importing


class EvidenceExportTests(FixtureRepo):
    def snapshot(self):
        # The fixture supplies only graph-relevant files; metadata validation is tested separately.
        with patch.object(ieantn, "check_graph", return_value=True):
            return ieantn.evidence_snapshot()

    def test_bridge_sources_are_conjunctive_and_spares_are_not_edges(self):
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", LITERATURE)
        self.write_node("C.v1", bridged_from(["B.v1.main", "A.v1.main"]))
        document = self.snapshot()
        result = next(c for c in document["conclusions"] if c["key"] == "C.v1.main")
        self.assertEqual(result["requirements"], [
            {"conclusion": "A.v1.main", "relation": "bridge"},
            {"conclusion": "B.v1.main", "relation": "bridge"},
        ])
        self.assertEqual(result["unproved_leaves"], ["A.v1.main", "B.v1.main"])
        self.assertNotIn("_dir", json.dumps(document))

    def test_export_leaf_sets_agree_with_existing_report_walk(self):
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", importing("A.v1"))
        document = self.snapshot()
        index = ieantn.index_conclusions(ieantn.load_nodes())
        for entry in document["conclusions"]:
            self.assertEqual(entry["unproved_leaves"],
                             sorted(set(ieantn.unjustified_leaves(index, entry["key"]))))
        self.assertEqual(document, self.snapshot())

    def test_broken_receipt_is_an_unproved_leaf(self):
        body = LITERATURE.replace("kind: literature", "kind: lean-comparator")
        self.write_node("A.v1", body)
        document = self.snapshot()
        entry = document["conclusions"][0]
        self.assertEqual(entry["receipt"]["state"], "BROKEN")
        self.assertEqual(entry["evidence"], "lean-comparator-drifted")
        self.assertEqual(entry["unproved_leaves"], ["A.v1.main"])

    def test_inactive_nodes_are_opt_in(self):
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", LITERATURE, status="inactive")
        self.assertEqual([n["id"] for n in self.snapshot()["nodes"]], ["A.v1"])
        with patch.object(ieantn, "check_graph", return_value=True):
            all_nodes = ieantn.evidence_snapshot(include_inactive=True)
        self.assertEqual([n["id"] for n in all_nodes["nodes"]], ["A.v1", "B.v1"])
        self.assertTrue(all_nodes["nodes"][1]["inactive"])

    def test_validation_errors_never_pollute_stdout(self):
        out, err = io.StringIO(), io.StringIO()
        def invalid():
            print("unknown requirement")
            return False
        with patch.object(ieantn, "check_graph", side_effect=invalid):
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                self.assertFalse(ieantn.export_evidence())
        self.assertEqual(out.getvalue(), "")
        self.assertIn("unknown requirement", err.getvalue())

    def test_json_only_stdout_and_yaml_dates(self):
        self.write_node("A.v1", LITERATURE)
        out = io.StringIO()
        with patch.object(ieantn, "check_graph", return_value=True):
            with contextlib.redirect_stdout(out):
                self.assertTrue(ieantn.export_evidence())
        self.assertEqual(json.loads(out.getvalue()), self.snapshot())
        self.assertEqual(ieantn.evidence_json_default(datetime.date(2026, 11, 11)), "2026-11-11")
        with self.assertRaises(TypeError):
            ieantn.evidence_json_default(object())

    def test_dangling_reference_is_not_silently_omitted(self):
        self.write_node("A.v1", importing("Missing.v1"))
        with self.assertRaisesRegex(ValueError, "unknown requirement"):
            self.snapshot()

