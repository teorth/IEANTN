"""Lifecycle commands must preserve metadata references as well as import edges."""
from test_ieantn import FixtureRepo, LITERATURE, bridged, ieantn


class TestLifecycleReferences(FixtureRepo):
    def setup_bridge(self):
        self.write_node("A.v1", LITERATURE)
        self.write_node("B.v1", bridged("A.v1.main"))
        bridge = self.root / "IEANTN" / "Bridges" / "a.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text("import IEANTN.Nodes.A.v1.Conclusions\n")

    def test_deactivation_refuses_to_dangle_a_bridge_source(self):
        self.setup_bridge()
        self.assertTrue(ieantn.check_graph())
        self.assertFalse(ieantn.deactivate(["A.v1"], "Retired."))
        self.assertTrue(ieantn.check_graph())

    def test_reactivation_requires_bridge_sources_first(self):
        self.setup_bridge()
        # Bridges are always in the core build. Retire this one before its
        # source, and restore it only once that source is live again.
        bridge = self.root / "IEANTN" / "Bridges" / "a.lean"
        source = bridge.read_bytes()
        bridge.unlink()
        self.assertTrue(ieantn.deactivate(["A.v1", "B.v1"], "Retired."))
        self.assertTrue(ieantn.check_closure())
        self.assertFalse(ieantn.reactivate("B.v1"))
        self.assertTrue(ieantn.reactivate("A.v1"))
        bridge.write_bytes(source)
        self.assertTrue(ieantn.reactivate("B.v1"))
        self.assertTrue(ieantn.check_graph())
        self.assertTrue(ieantn.check_closure())

    def test_deprecation_replacement_must_remain_live(self):
        self.write_node("A.v1", LITERATURE)
        self.write_node("A.v2", LITERATURE)
        self.assertTrue(ieantn.deprecate("A.v1", "A.v2"))
        self.assertFalse(ieantn.deactivate(["A.v2"], "Retired."))
        self.assertTrue(ieantn.check_graph())
