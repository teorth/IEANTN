"""Closing a section must not drop the namespace wrapped around a bridge."""
from test_ieantn import FixtureRepo, ieantn


class TestBridgeSections(FixtureRepo):
    def test_named_section_does_not_pop_the_enclosing_namespace(self) -> None:
        text = (
            "namespace Demo\n"
            "section Helper -- λ local names\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Helper\n"
            "end Demo\n"
        )
        path = self.root / "bridge.lean"
        path.write_text(text, encoding="utf-8")
        text = path.read_text(encoding="utf-8")
        found = ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"})
        self.assertEqual(found, [("Demo.from_b", ["B.v1.main"])])

    def test_anonymous_section_does_not_pop_the_enclosing_namespace(self) -> None:
        text = (
            "namespace Demo\n"
            "section\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end\n"
            "end Demo\n"
        )
        found = ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"})
        self.assertEqual(found, [("Demo.from_b", ["B.v1.main"])])

    def test_end_still_closes_a_dotted_namespace(self) -> None:
        text = (
            "namespace Demo.Inner\n"
            "theorem from_b (h : B.v1.main) : A.v1.main := trivial\n"
            "end Inner\n"
            "theorem outside (h : B.v1.main) : A.v1.main := trivial\n"
            "end Demo\n"
        )
        found = ieantn.bridge_theorems(text, "A.v1.main", {"B.v1.main"})
        self.assertEqual(
            [name for name, _binders in found],
            ["Demo.Inner.from_b", "Demo.outside"],
        )
