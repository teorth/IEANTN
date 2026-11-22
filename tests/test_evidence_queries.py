"""Behavioral tests for explanations, hypothetical routes, impact and whole-node budgets."""
import copy
import importlib.util
import io
import json
import pathlib
import subprocess
import sys
import tempfile
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

    def test_plan_deduplicates_runs_by_node_and_covers_every_conclusion(self):
        d = document(entry("A.v1.one", "lean-comparator-stale", receipt={"state": "yellow"}),
                     entry("A.v1.two", "lean-comparator-stale", receipt={"state": "yellow"}))
        result = query.refresh_plan(query.EvidenceGraph(d), {"A.v1": 20}, 30)
        self.assertEqual(len(result["runs"]), 1)
        self.assertEqual(result["runs"][0]["covers"], ["A.v1.one", "A.v1.two"])
        self.assertEqual(result["known_selected_seconds"], 20)
        self.assertFalse(result["dispatches"])

    def test_unknown_cost_never_silently_fits_finite_budget(self):
        d = document(entry("A.v1.main", "lean-comparator-stale", receipt={"state": "yellow"}))
        result = query.refresh_plan(query.EvidenceGraph(d), budget=100)
        self.assertFalse(result["runs"][0]["selected"])
        self.assertEqual(result["runs"][0]["decision"], "unknown-cost")

    def test_nonfinite_and_boolean_costs_are_rejected(self):
        graph = query.EvidenceGraph(self.diamond())
        for value in [True, False, float("inf"), float("-inf"), float("nan"), 0, -1, "20", None]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                query.refresh_plan(graph, {"A.v1": value})
            with self.subTest(budget=value), self.assertRaises(ValueError):
                # None is the valid unbounded-budget sentinel.
                query.refresh_plan(graph, budget=value if value is not None else "unbounded")
        for costs in [[], 20, {1: 20}]:
            with self.subTest(costs=costs), self.assertRaises(ValueError):
                query.refresh_plan(graph, costs)

    def ranked_plan_document(self):
        entries = [entry(f"{node}.v1.main", "lean-comparator-drifted" if state == "BROKEN"
                         else "lean-comparator-stale", receipt={"state": state})
                   for node, state in [("A", "yellow"), ("B", "orange"),
                                       ("C", "churn"), ("Z", "BROKEN")]]
        # Less urgent nodes deliberately have greater downstream reach.
        for node, count in [("A", 3), ("B", 2), ("C", 1)]:
            entries += [entry(f"User{node}{i}.v1.main",
                              requirements=[(f"{node}.v1.main", "import")])
                        for i in range(count)]
        return document(*entries)

    def test_plan_ranks_all_four_states_before_downstream_reach(self):
        d = self.ranked_plan_document()
        original = copy.deepcopy(d)
        result = query.refresh_plan(query.EvidenceGraph(d))
        self.assertEqual([r["node"] for r in result["runs"]], ["Z.v1", "C.v1", "B.v1", "A.v1"])
        self.assertEqual([r["downstream_reach"] for r in result["runs"]], [1, 2, 3, 4])
        self.assertTrue(all(r["selected"] for r in result["runs"]))
        self.assertEqual(result["known_selected_seconds"], 0)
        self.assertTrue(result["costs_are_estimates"])
        self.assertFalse(result["dispatches"])
        self.assertEqual(d, original)

    def test_plan_shared_node_uses_most_urgent_state_and_union_reach(self):
        d = document(
            entry("Z.v1.one", "lean-comparator-stale", receipt={"state": "yellow"}),
            entry("Z.v1.two", "lean-comparator-stale", receipt={"state": "churn"}),
            entry("Z.v1.healthy", "lean-comparator", receipt={"state": "green"}),
            entry("A.v1.main", "lean-comparator-stale", receipt={"state": "orange"}),
            entry("User.v1.main", requirements=[("Z.v1.one", "import"), ("Z.v1.two", "import")]))
        result = query.refresh_plan(query.EvidenceGraph(d), {"Z.v1": 20, "A.v1": 20}, 20)
        self.assertEqual([r["node"] for r in result["runs"]], ["Z.v1", "A.v1"])
        run = result["runs"][0]
        self.assertEqual(run["states"], ["churn", "yellow"])
        self.assertEqual(run["reasons"], ["Z.v1.one", "Z.v1.two"])
        self.assertEqual(run["covers"], ["Z.v1.healthy", "Z.v1.one", "Z.v1.two"])
        self.assertEqual(run["downstream_reach"], 3)
        self.assertEqual(result["known_selected_seconds"], 20)
        self.assertTrue(run["selected"])
        self.assertEqual(result["runs"][1]["decision"], "over-budget")

    def test_plan_equal_rank_uses_reach_then_deterministic_node_ties(self):
        for state in ["BROKEN", "churn", "orange", "yellow"]:
            entries = [entry(f"{node}.v1.main", "lean-comparator-drifted" if state == "BROKEN"
                             else "lean-comparator-stale", receipt={"state": state})
                       for node in ["C", "B", "A"]]
            entries += [entry("User.v1.main", requirements=[("C.v1.main", "import")]),
                        entry("Transitive.v1.main", requirements=[("User.v1.main", "import")])]
            for ordered in [entries, list(reversed(entries))]:
                with self.subTest(state=state, first=ordered[0]["key"]):
                    result = query.refresh_plan(query.EvidenceGraph(document(*ordered)))
                    self.assertEqual([r["node"] for r in result["runs"]], ["C.v1", "A.v1", "B.v1"])
                    self.assertEqual([r["downstream_reach"] for r in result["runs"]], [3, 1, 1])

    def test_plan_finite_budget_skips_unknown_and_expensive_runs_then_fills_exactly(self):
        graph = query.EvidenceGraph(self.ranked_plan_document())
        result = query.refresh_plan(graph, {"C.v1": 11, "B.v1": 6, "A.v1": 4.0}, 10)
        self.assertEqual([r["decision"] for r in result["runs"]],
                         ["unknown-cost", "over-budget", "selected", "selected"])
        self.assertEqual(result["known_selected_seconds"], 10)
        self.assertEqual(result["budget_seconds"], 10)
        self.assertIsNone(result["runs"][0]["estimated_seconds"])

    def test_plan_ignores_green_and_unreceipted_conclusions(self):
        graph = query.EvidenceGraph(document(
            entry("A.v1.main", "lean-comparator", receipt={"state": "green"}), entry("B.v1.main")))
        self.assertEqual(query.refresh_plan(graph)["runs"], [])

    def test_refresh_plan_cli_files_and_stdin_use_ranked_budget(self):
        d = self.ranked_plan_document()
        with tempfile.TemporaryDirectory() as temporary:
            directory = pathlib.Path(temporary)
            evidence, costs = directory / "evidence.json", directory / "costs.json"
            evidence.write_text(json.dumps(d), encoding="utf-8")
            costs.write_text(json.dumps({"C.v1": 11, "B.v1": 6, "A.v1": 4}), encoding="utf-8")
            for source in [[], ["--input", str(evidence)]]:
                with self.subTest(source=source):
                    process = subprocess.run(
                        [sys.executable, "-I", query.__file__, *source, "refresh-plan",
                         "--costs", str(costs), "--budget", "10"],
                        input=json.dumps(d), text=True, encoding="utf-8", capture_output=True, timeout=10)
                    self.assertEqual(process.returncode, 0, process.stderr)
                    self.assertEqual(process.stderr, "")
                    result = json.loads(process.stdout)
                    self.assertEqual([r["node"] for r in result["runs"]], ["Z.v1", "C.v1", "B.v1", "A.v1"])
                    self.assertEqual([r["decision"] for r in result["runs"]],
                                     ["unknown-cost", "over-budget", "selected", "selected"])
                    self.assertEqual(result["known_selected_seconds"], 10)
                    self.assertFalse(result["dispatches"])
                    self.assertTrue(result["costs_are_estimates"])

    def test_refresh_plan_cli_rejects_invalid_costs_and_budgets_without_json(self):
        with tempfile.TemporaryDirectory() as temporary:
            costs = pathlib.Path(temporary) / "costs.json"
            cases = [(["--costs", str(costs)], content)
                     for content in ['{"A.v1": NaN}', '{"A.v1": 1e999}', '{"A.v1": true}']]
            cases += [(["--budget", value], '{}') for value in ["nan", "inf", "0", "-1"]]
            for arguments, content in cases:
                with self.subTest(arguments=arguments, content=content):
                    costs.write_text(content, encoding="utf-8")
                    process = subprocess.run(
                        [sys.executable, "-I", query.__file__, "refresh-plan", *arguments],
                        input=json.dumps(self.ranked_plan_document()), text=True, encoding="utf-8",
                        capture_output=True, timeout=10)
                    self.assertEqual(process.returncode, 1, process.stderr)
                    self.assertEqual(process.stdout, "")
                    self.assertIn("error:", process.stderr)

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

