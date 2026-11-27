"""Conservative network-hypothesis matching in simple namespace contexts.

The graph is not a Lean imported environment. Multiple candidate declarations and
active section variables must be refused, not resolved by guessing. Unique short
names remain supported, without claiming to implement Lean elaboration.
"""
import contextlib
import io
import json
import unittest
import unittest.mock

from test_ieantn import LITERATURE, FixtureRepo, bridged, ieantn


def _decl() -> dict:
    line = "def main : Prop := True"
    return dict(
        module="IEANTN.Nodes.A.v1.Conclusions", name="A.v1.main",
        startLine=5, startCol=0, endLine=5, endCol=len(line),
        nameStartLine=5, nameStartCol=4, nameEndLine=5, nameEndCol=8,
    )


class TestBridgeBinderResolution(FixtureRepo):
    def spin(self, key: str = "A.v1.main") -> tuple[bool, str]:
        result = ieantn.subprocess.CompletedProcess(
            [], 0, json.dumps({"declarations": [_decl()]}), ""
        )
        output = io.StringIO()
        with unittest.mock.patch.object(ieantn, "receipt_state", return_value=None), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=result), \
             contextlib.redirect_stdout(output):
            ok = ieantn.spinoff(key, "export", False)
        return ok, output.getvalue()

    def test_unimported_namespace_candidate_does_not_replace_root(self) -> None:
        text = (
            "import IEANTN.Nodes.A.v1.Conclusions\n"
            "import IEANTN.Nodes.B.v1.Conclusions\n"
            "namespace Demo\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := by rfl\n"
            "end Demo\n"
        )
        # `known` is the entire graph, not the imported Lean environment. Without
        # elaboration we cannot choose either candidate, even though Lean sees the root.
        known = {"A.v1.main", "B.v1.main", "Demo.B.v1.main"}
        self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", known), [])

    def test_imported_namespace_candidate_does_not_fall_back_to_root(self) -> None:
        for imports in (
            "import IEANTN.Nodes.Demo.B.v1.Conclusions\n",
            "import IEANTN.Nodes.B.v1.Conclusions\n"
            "import IEANTN.Nodes.Demo.B.v1.Conclusions\n",
        ):
            with self.subTest(imports=imports):
                text = (
                    "import IEANTN.Nodes.A.v1.Conclusions\n" + imports
                    + "namespace Demo\n"
                    "theorem from_b (h : B.v1.main) : A.v1.main := by rfl\n"
                    "end Demo\n"
                )
                # Returning the root on ambiguity would be wrong in this direction.
                known = {"A.v1.main", "B.v1.main", "Demo.B.v1.main"}
                self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", known), [])

    def test_section_local_prop_is_not_a_network_hypothesis(self) -> None:
        text = (
            "namespace B.v1\n"
            "section\n"
            "variable (main : Prop)\n"
            "theorem to_a (h : main) : A.v1.main := by rfl\n"
            "end\n"
            "end B.v1\n"
        )
        self.assertEqual(
            ieantn.bridge_theorems(text, "A.v1.main", {"A.v1.main", "B.v1.main"}), []
        )

    def test_variable_scope_rejection_ends_only_with_its_own_scope(self) -> None:
        text = (
            "namespace B.v1\n"
            "section Outer\n"
            "variable (main : Prop)\n"
            "section Inner\n"
            "theorem inside (h : main) : A.v1.main := by rfl\n"
            "end Inner\n"
            "theorem still_inside (h : main) : A.v1.main := by rfl\n"
            "end Outer\n"
            "theorem outside (h : main) : A.v1.main := by rfl\n"
            "end B.v1\n"
        )
        self.assertEqual(
            ieantn.bridge_theorems(text, "A.v1.main", {"A.v1.main", "B.v1.main"}),
            [("B.v1.outside", ["B.v1.main"])],
        )

    def test_variable_context_is_refused_even_if_a_parameter_might_be_unused(self) -> None:
        text = (
            "namespace B.v1\nsection\nvariable (unused : Prop)\n"
            "theorem to_a (h : B.v1.main) : A.v1.main := by rfl\n"
            "end\nend B.v1\n"
        )
        # Deliberate false negative: source scanning cannot recover Lean's telescope.
        self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"}), [])

    def test_variable_context_is_restored_after_section_or_namespace_end(self) -> None:
        for opening, closing in (
            ("section", "end"),
            ("section Local", "end Local"),
            ("namespace Local", "end Local"),
        ):
            with self.subTest(opening=opening):
                text = (
                    f"namespace B.v1\n{opening}\nvariable (main : Prop)\n"
                    "theorem inside (h : main) : A.v1.main := by rfl\n"
                    f"{closing}\n"
                    "theorem outside (h : main) : A.v1.main := by rfl\n"
                    "end B.v1\n"
                )
                self.assertEqual(
                    ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"}),
                    [("B.v1.outside", ["B.v1.main"])],
                )

    def test_top_level_variable_context_is_not_cleared_by_nested_end(self) -> None:
        text = (
            "variable (main : Prop)\nnamespace B.v1\nsection\nend\n"
            "theorem to_a (h : main) : A.v1.main := by rfl\nend B.v1\n"
        )
        self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"}), [])

    def test_composition_refuses_ambiguous_import_visibility(self) -> None:
        self.write_node("B.v1", LITERATURE)
        self.write_node("Demo.B.v1", LITERATURE)
        self.write_node("A.v1", bridged("B.v1.main"))
        bridge = self.root / "IEANTN" / "Bridges" / "a.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text(
            "import IEANTN.Nodes.A.v1.Conclusions\n"
            "import IEANTN.Nodes.B.v1.Conclusions\n"
            "namespace Demo\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n",
            encoding="utf-8",
        )
        ok, text = self.spin()
        self.assertFalse(ok, text)
        self.assertIn("Refusing to guess an application.", text)
        self.assertFalse((self.root / "export").exists())

    def test_composition_refuses_section_local_prop(self) -> None:
        self.write_node("B.v1", LITERATURE)
        self.write_node("A.v1", bridged("B.v1.main"))
        bridge = self.root / "IEANTN" / "Bridges" / "a.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text(
            "namespace B.v1\nsection\nvariable (main : Prop)\n"
            "theorem to_a (h : main) : A.v1.main := trivial\n"
            "end\nend B.v1\n",
            encoding="utf-8",
        )
        ok, text = self.spin()
        self.assertFalse(ok, text)
        self.assertIn("Refusing to guess an application.", text)
        self.assertFalse((self.root / "export").exists())

    def test_ambiguous_binder_is_not_resolved_by_graph_membership(self) -> None:
        text = (
            "namespace Demo\n"
            "-- λ\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        known = {"A.v1.main", "B.v1.main", "Demo.B.v1.main"}
        self.assertIsNone(ieantn._resolve_binder_type("B.v1.main", ["Demo"], known))
        self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", known), [])

    def test_a_short_binder_is_prefixed_with_the_enclosing_namespace(self) -> None:
        text = (
            "namespace B.v1\n"
            "theorem to_a (h : main) : A.v1.main := trivial\n"
            "end B.v1\n"
        )
        found = ieantn.bridge_theorems(text, "A.v1.main", {"A.v1.main", "B.v1.main"})
        self.assertEqual(found, [("B.v1.to_a", ["B.v1.main"])])

    def test_a_root_binder_stays_root_when_no_longer_name_exists(self) -> None:
        text = (
            "namespace Demo\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        found = ieantn.bridge_theorems(text, "A.v1.main", {"A.v1.main", "B.v1.main"})
        self.assertEqual(found, [("Demo.from_b", ["B.v1.main"])])

    def test_qualified_binder_survives_a_named_section_end(self) -> None:
        text = (
            "namespace Demo\n"
            "section Helper\n"
            "end Helper\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        known = {"Demo.B.v1.main"}
        self.assertEqual(
            ieantn.bridge_theorems(text, "A.v1.main", known),
            [("Demo.from_b", ["Demo.B.v1.main"])],
        )

    def test_unqualified_binder_survives_nested_section_ends(self) -> None:
        text = (
            "namespace Demo.B.v1\n"
            "section Helper\n"
            "section\n"
            "theorem inside (h : main) : A.v1.main := trivial\n"
            "end\n"
            "theorem after_anonymous (h : main) : A.v1.main := trivial\n"
            "end Helper\n"
            "theorem after_named (h : main) : A.v1.main := trivial\n"
            "end Demo.B.v1\n"
            "theorem outside (h : B.v1.main) : A.v1.main := trivial\n"
        )
        self.assertEqual(
            ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main", "Demo.B.v1.main"}),
            [("Demo.B.v1.inside", ["Demo.B.v1.main"]),
             ("Demo.B.v1.after_anonymous", ["Demo.B.v1.main"]),
             ("Demo.B.v1.after_named", ["Demo.B.v1.main"]),
             ("outside", ["B.v1.main"])],
        )

    def test_nested_namespace_accepts_only_a_unique_known_candidate(self) -> None:
        text = (
            "namespace Demo.Inner\n"
            "section Helper\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Helper\n"
            "end Demo.Inner\n"
        )
        candidates = {"B.v1.main", "Demo.B.v1.main", "Demo.Inner.B.v1.main"}
        for expected in sorted(candidates):
            with self.subTest(expected=expected):
                self.assertEqual(
                    ieantn.bridge_theorems(text, "A.v1.main", {expected}),
                    [("Demo.Inner.from_b", [expected])],
                )
        for known in (candidates, {"B.v1.main", "Demo.B.v1.main"}):
            with self.subTest(known=known):
                self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", known), [])

    def test_open_only_binder_is_not_guessed(self) -> None:
        text = (
            "open B.v1\n"
            "namespace Demo\n"
            "section Helper\n"
            "end Helper\n"
            "theorem from_b (h : main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        self.assertEqual(ieantn._resolve_binder_type("main", ["Demo"], {"B.v1.main"}), "main")
        self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"}), [])

    def test_unknown_binders_are_unchanged_and_rejected(self) -> None:
        for written in ("missing", "Missing.v1.main", "B.v1.main ∧ True"):
            with self.subTest(written=written):
                known = {"B.v1.main"}
                self.assertEqual(ieantn._resolve_binder_type(written, ["Demo"], known), written)
                text = (
                    "namespace Demo\nsection\nend\n"
                    f"theorem from_b (h : {written}) : A.v1.main := trivial\n"
                    "end Demo\n"
                )
                self.assertEqual(ieantn.bridge_theorems(text, "A.v1.main", known), [])

    def test_dotted_theorem_is_only_accepted_outside_a_namespace(self) -> None:
        text = (
            "section Helper\n"
            "theorem Demo.from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Helper\n"
            "namespace Demo\nsection\nend\n"
            "theorem Inner.from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        self.assertEqual(
            ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main", "Demo.B.v1.main"}),
            [("Demo.from_b", ["B.v1.main"])],
        )

    def test_composition_refuses_open_only_and_unknown_binders(self) -> None:
        self.write_node("B.v1", LITERATURE)
        self.write_node("A.v1", bridged("B.v1.main"))
        bridge = self.root / "IEANTN" / "Bridges" / "a.lean"
        bridge.parent.mkdir(parents=True)
        for written in ("main", "Missing.v1.main"):
            with self.subTest(written=written):
                bridge.write_text(
                    "open B.v1\nnamespace Demo\nsection Helper\nend Helper\n"
                    f"theorem from_b (h : {written}) : A.v1.main := trivial\n"
                    "end Demo\n",
                    encoding="utf-8",
                )
                ok, text = self.spin()
                self.assertFalse(ok)
                self.assertIn("Refusing to guess an application.", text)
                self.assertFalse((self.root / "export").exists())

    def test_composition_applies_a_unique_namespace_hypothesis(self) -> None:
        self.write_node("Demo.B.v1", LITERATURE)
        body = bridged("Demo.B.v1.main").replace(
            "bridge: IEANTN/Bridges/a.lean",
            "bridge: IEANTN/Bridges/Demo/FromB.lean",
        )
        self.write_node("A.v1", body)
        bridge = self.root / "IEANTN" / "Bridges" / "Demo" / "FromB.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text(
            "import IEANTN.Nodes.A.v1.Conclusions\n"
            "import IEANTN.Nodes.Demo.B.v1.Conclusions\n"
            "namespace Demo\n"
            "-- the λ in this comment must survive a UTF-8 round trip\n"
            "section Helper\n"
            "end Helper\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n",
            encoding="utf-8",
        )
        ok, text = self.spin()
        self.assertTrue(ok, text)
        solution = (self.root / "export" / "Solution.lean").read_text(encoding="utf-8")
        self.assertIn("(Demo.from_b demo_b_v1_main)", solution)
        self.assertNotIn("(Demo.from_b b_v1_main)", solution)

    def test_a_short_binder_composes_through_the_bridge_under_it(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("B.v1", bridged("Leaf.v1.main"))
        body = bridged("B.v1.main").replace(
            "bridge: IEANTN/Bridges/a.lean",
            "bridge: IEANTN/Bridges/A/ToA.lean",
        )
        self.write_node("A.v1", body)
        (self.root / "IEANTN" / "Bridges").mkdir(parents=True, exist_ok=True)
        (self.root / "IEANTN" / "Bridges" / "a.lean").write_text(
            "theorem to_b (h : Leaf.v1.main) : B.v1.main := trivial\n",
            encoding="utf-8",
        )
        nested = self.root / "IEANTN" / "Bridges" / "A" / "ToA.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text(
            "namespace B.v1\n"
            "section Helper\n"
            "section\n"
            "-- λ\n"
            "end\n"
            "end Helper\n"
            "theorem to_a (h : main) : A.v1.main := trivial\n"
            "end B.v1\n",
            encoding="utf-8",
        )
        ok, text = self.spin()
        self.assertTrue(ok, text)
        solution = (self.root / "export" / "Solution.lean").read_text(encoding="utf-8")
        self.assertIn("(B.v1.to_a (to_b leaf_v1_main))", solution)


if __name__ == "__main__":
    unittest.main()
