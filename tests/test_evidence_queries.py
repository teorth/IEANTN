"""Behavioral tests for explanations, hypothetical routes, impact and whole-node budgets."""
import copy
import importlib.util
import io
import pathlib
import unittest

_SPEC = importlib.util.spec_from_file_location(
    "evidence_queries", pathlib.Path(__file__).resolve().parent.parent / "scripts/evidence_queries.py")
assert _SPEC and _SPEC.loader
query = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(query)


def entry(key, kind="literature", requirements=(), receipt=None, spares=()):
    return {"key": key, "node": key.rsplit(".", 1)[0], "evidence": kind,
            "fingerprint": "old", "designated": "main", "imports_status": "identified",
            "requirements": [{"conclusion": target, "relation": relation}
                             for target, relation in requirements],
            "receipt": receipt, "justifications": list(spares), "source": key + ".lean"}


def document(*entries):
    return {"schema_version": 1, "conclusions": list(entries)}


class QueryTests(unittest.TestCase):
    def diamond(self):
        return document(
            entry("A.v1.main"),
            entry("B.v1.main", "bridged", [("A.v1.main", "bridge")]),
            entry("C.v1.main", "bridged", [("A.v1.main", "bridge")]),
            entry("D.v1.main", "bridged", [("B.v1.main", "bridge"), ("C.v1.main", "bridge")]),
        )

    def test_diamond_gives_a_shortest_witness_without_losing_and_premises(self):
        graph = query.EvidenceGraph(self.diamond())
        result = graph.explain("D.v1.main")
        self.assertEqual(result["unproved_leaves"], ["A.v1.main"])
        self.assertEqual(len(result["witness_paths"]), 1)
        self.assertEqual([s["conclusion"] for s in result["witness_paths"][0]["path"]],
                         ["D.v1.main", "B.v1.main", "A.v1.main"])
        self.assertEqual(len(graph.edges["D.v1.main"]), 2)
        self.assertEqual(result["requirements_semantics"], "all")

    def test_unproved_intermediate_remains_a_leaf_as_well_as_its_inputs(self):
        graph = query.EvidenceGraph(document(
            entry("A.v1.main"), entry("B.v1.main", requirements=[("A.v1.main", "import")])))
        self.assertEqual(graph.explain("B.v1.main")["unproved_leaves"],
                         ["A.v1.main", "B.v1.main"])

    def test_stale_receipt_does_not_add_a_leaf_but_broken_receipt_does(self):
        d = document(entry("A.v1.main", "lean-comparator-stale", receipt={"state": "yellow"}))
        self.assertEqual(query.EvidenceGraph(d).leaves["A.v1.main"], set())
        d["conclusions"][0]["evidence"] = "lean-comparator-drifted"
        d["conclusions"][0]["receipt"]["state"] = "BROKEN"
        self.assertEqual(query.EvidenceGraph(d).leaves["A.v1.main"], {"A.v1.main"})

    def test_combined_cycle_and_dangling_premises_fail(self):
        with self.assertRaisesRegex(ValueError, "cycle"):
            query.EvidenceGraph(document(
                entry("A.v1.main", "bridged", [("B.v1.main", "bridge")]),
                entry("B.v1.main", "literature", [("A.v1.main", "import")])))
        with self.assertRaisesRegex(ValueError, "unknown requirement"):
            query.EvidenceGraph(document(entry("A.v1.main", requirements=[("M.v1.main", "import")])))

    def test_unassessed_verified_label_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "standing receipt"):
            query.EvidenceGraph(document(entry("A.v1.main", "lean-comparator")))

    def test_alternative_exposes_new_assumptions_without_modifying_input(self):
        d = document(entry("A.v1.main"), entry("B.v1.main"),
                     entry("C.v1.main", "bridged", [("A.v1.main", "bridge")],
                           spares=[{"id": "other", "kind": "bridged", "from": "B.v1.main"}]),
                     entry("D.v1.main", "bridged", [("C.v1.main", "bridge")]))
        original = copy.deepcopy(d)
        result = query.EvidenceGraph(d).alternative("C.v1.main", "other")
        self.assertEqual(d, original)
        self.assertEqual(result["changes"][-1]["gained"], ["B.v1.main"])
        self.assertEqual(result["changes"][-1]["discharged"], ["A.v1.main"])
        self.assertFalse(result["writes_metadata"])

    def test_spare_lean_route_without_assessment_is_never_claimed_verified(self):
        d = document(entry("A.v1.main", spares=[{"id": "proof", "kind": "lean-comparator"}]))
        result = query.EvidenceGraph(d).alternative("A.v1.main", "proof")
        self.assertEqual(result["changes"][0]["after"], ["A.v1.main"])
        self.assertTrue(result["warnings"])

    def test_hypothetical_cycle_is_rejected(self):
        d = document(entry("A.v1.main", spares=[
                         {"id": "bad", "kind": "bridged", "from": "B.v1.main"}]),
                     entry("B.v1.main", "bridged", [("A.v1.main", "bridge")]))
        with self.assertRaisesRegex(ValueError, "cycle"):
            query.EvidenceGraph(d).alternative("A.v1.main", "bad")

    def test_impact_finds_transitive_users_and_a_concrete_route(self):
        d = self.diamond()
        new = copy.deepcopy(d)
        new["conclusions"][0]["fingerprint"] = "changed"
        result = query.impact(query.EvidenceGraph(d), query.EvidenceGraph(new))
        finding = result["changes"][0]
        self.assertIn("D.v1.main", finding["downstream"])
        witness = next(p for p in finding["witness_paths"] if p["conclusion"] == "D.v1.main")
        self.assertEqual(witness["path_to_changed"][-1], "A.v1.main")
        self.assertIn("new node version", finding["repair_advice"][0])




    def test_duplicate_keys_and_unsupported_schema_fail(self):
        with self.assertRaisesRegex(ValueError, "duplicate JSON"):
            query.load_document(io.StringIO('{"schema_version":1,"schema_version":1}'))
        with self.assertRaisesRegex(ValueError, "unsupported"):
            query.EvidenceGraph({"schema_version": 2, "conclusions": []})

    def test_long_chain_does_not_depend_on_python_recursion_limit(self):
        entries = [entry("A.v1.x0")]
        entries += [entry(f"A.v1.x{i}", "bridged", [(f"A.v1.x{i-1}", "bridge")])
                    for i in range(1, 1100)]
        graph = query.EvidenceGraph(document(*entries))
        self.assertEqual(graph.leaves["A.v1.x1099"], {"A.v1.x0"})

