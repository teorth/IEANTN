"""`docs/graph.html`: the graph drawn, because Markdown could no longer hold it.

The layout is computed when the file is generated rather than in the browser, which is what lets
CI diff the result like any other view -- so these tests are mostly about the two properties that
buys: it is reproducible, and it is a drawing nobody has to squint at because two boxes landed in
the same place.
"""
import re
import xml.etree.ElementTree as ET

from test_ieantn import FixtureRepo, LITERATURE, bridged, ieantn, importing

SVG = "{http://www.w3.org/2000/svg}"


def chain(length: int) -> list[tuple[str, str]]:
    return [(f"v{i}", f"v{i + 1}") for i in range(length - 1)]


class TestLayeredLayout(FixtureRepo):
    def test_an_arrow_always_points_rightwards(self) -> None:
        """Which is what makes the reach of an arrow mean something."""
        edges = chain(5) + [("v0", "v4")]
        rank = {f"v{i}": (f"v{i}",) for i in range(5)}
        place = ieantn.layered_layout(list(rank), edges, rank)
        for source, target in edges:
            self.assertLess(place[source][0], place[target][0], f"{source} -> {target}")

    def test_the_layer_is_the_longest_path_not_the_shortest(self) -> None:
        """A short cut must not pull a box left of something that depends on it."""
        rank = {f"v{i}": (f"v{i}",) for i in range(4)}
        place = ieantn.layered_layout(list(rank), chain(4) + [("v0", "v3")], rank)
        self.assertEqual([place[f"v{i}"][0] for i in range(4)], [0, 1, 2, 3])

    def test_two_boxes_never_share_a_slot_in_a_layer(self) -> None:
        rank = {f"v{i}": (f"v{i}",) for i in range(6)}
        edges = [("v0", "v3"), ("v1", "v3"), ("v2", "v3"), ("v4", "v5")]
        place = ieantn.layered_layout(list(rank), edges, rank)
        self.assertEqual(len(set(place.values())), len(place))

    def test_it_does_not_hang_on_a_cycle(self) -> None:
        """`check_graph` rejects one, but a drawing command is not where to meet it."""
        rank = {"a": ("a",), "b": ("b",)}
        place = ieantn.layered_layout(["a", "b"], [("a", "b"), ("b", "a")], rank)
        self.assertEqual(len(place), 2)

    def test_the_same_graph_always_lays_out_the_same_way(self) -> None:
        """The view is committed and diffed, so the layout may not depend on iteration order."""
        rank = {f"v{i}": (f"v{i}",) for i in range(8)}
        edges = [("v0", "v4"), ("v1", "v4"), ("v2", "v5"), ("v3", "v5"), ("v4", "v6"),
                 ("v5", "v6"), ("v6", "v7")]
        first = ieantn.layered_layout(list(rank), edges, rank)
        for _ in range(3):
            self.assertEqual(ieantn.layered_layout(list(reversed(list(rank))), edges, rank),
                             first)


class TestDrawnPage(FixtureRepo):
    def build(self) -> str:
        self.write_node("Leaf.v1", LITERATURE)
        self.write_node("Mid.v1", importing("Leaf.v1"))
        self.write_node("Alone.v1", LITERATURE)
        bridge = self.root / "IEANTN" / "Bridges" / "a.lean"
        bridge.parent.mkdir(parents=True)
        bridge.write_text("import IEANTN.Nodes.Leaf.v1.Conclusions\n", encoding="utf-8")
        self.write_node("Bridged.v1", bridged("Leaf.v1.main"))
        return ieantn.render_graph_page(ieantn.load_nodes())

    def drawings(self, page: str) -> list[ET.Element]:
        return [ET.fromstring(found) for found in re.findall(r"<svg\b.*?</svg>", page, re.S)]

    def test_every_drawing_is_well_formed_svg(self) -> None:
        self.assertEqual(len(self.drawings(self.build())), 2)

    def test_no_two_boxes_overlap(self) -> None:
        for drawing in self.drawings(self.build()):
            placed = []
            for group in drawing.iter(f"{SVG}g"):
                rect = group.find(f"./{SVG}a/{SVG}rect")
                if rect is None:
                    continue
                placed.append((float(rect.get("x")), float(rect.get("y")),
                               float(rect.get("width")), float(rect.get("height"))))
            for first in range(len(placed)):
                for second in range(first + 1, len(placed)):
                    ax, ay, aw, ah = placed[first]
                    bx, by, bw, bh = placed[second]
                    self.assertFalse(
                        ax < bx + bw and bx < ax + aw and ay < by + bh and by < ay + ah,
                        f"{placed[first]} overlaps {placed[second]}")

    def test_every_box_is_inside_the_canvas(self) -> None:
        """An SVG does not clip, so a box outside the viewBox is simply invisible."""
        for drawing in self.drawings(self.build()):
            width, height = (float(value) for value in drawing.get("viewBox").split()[2:])
            for rect in drawing.iter(f"{SVG}rect"):
                self.assertLessEqual(float(rect.get("x")) + float(rect.get("width")), width)
                self.assertLessEqual(float(rect.get("y")) + float(rect.get("height")), height)

    def test_an_edge_joins_two_boxes_that_were_drawn(self) -> None:
        for drawing in self.drawings(self.build()):
            keys = {group.get("data-key") for group in drawing.iter(f"{SVG}g")
                    if "box" in (group.get("class") or "")}
            for path in drawing.iter(f"{SVG}path"):
                if path.get("data-from"):
                    self.assertIn(path.get("data-from"), keys)
                    self.assertIn(path.get("data-to"), keys)

    def test_a_claim_with_no_edges_is_listed_rather_than_drawn(self) -> None:
        """41 of the real network's conclusions have no edge at all. Drawing them among the rest
        cost most of the width and said nothing."""
        page = self.build()
        self.assertIn("Stands alone", page)
        drawn = {group.get("data-key") for drawing in self.drawings(page)
                 for group in drawing.iter(f"{SVG}g")
                 if "box" in (group.get("class") or "")}
        self.assertNotIn("Alone.v1.main", drawn)
        self.assertIn('data-key="Alone.v1.main"', page)

    def test_a_bridge_is_a_hexagon_between_its_premise_and_its_target(self) -> None:
        page = self.build()
        claims = self.drawings(page)[0]
        hexagons = [group.get("data-key") for group in claims.iter(f"{SVG}g")
                    if group.find(f"./{SVG}a/{SVG}polygon") is not None]
        self.assertEqual(len(hexagons), 1)
        edges = {(path.get("data-from"), path.get("data-to"))
                 for path in claims.iter(f"{SVG}path") if path.get("data-from")}
        self.assertIn(("Leaf.v1.main", hexagons[0]), edges)
        self.assertIn((hexagons[0], "Bridged.v1.main"), edges)

    def test_the_page_is_byte_for_byte_reproducible(self) -> None:
        self.assertEqual(self.build(), ieantn.render_graph_page(ieantn.load_nodes()))

    def test_graph_writes_and_checks_both_views(self) -> None:
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.graph(check_only=False))
        self.assertTrue((self.root / "docs" / "graph.html").is_file())
        self.assertTrue(ieantn.graph(check_only=True))
        (self.root / "docs" / "graph.html").write_text("stale", encoding="utf-8")
        self.assertFalse(ieantn.graph(check_only=True))

    def test_the_markdown_no_longer_carries_the_oversized_diagram(self) -> None:
        """GitHub's Mermaid viewer refuses a diagram over 50,000 characters, and the
        conclusion-level graph had reached 63,621. Whatever else changes, no block may approach
        that again."""
        self.write_node("A.v1", LITERATURE)
        rendered = ieantn.render_graph(ieantn.load_nodes())
        for block in re.findall(r"```mermaid\n(.*?)```", rendered, re.S):
            self.assertLess(len(block), 50_000)
        self.assertIn("docs/graph.html", rendered)

    def test_text_from_the_metadata_cannot_break_out_of_the_markup(self) -> None:
        directory = self.write_node("A.v1", LITERATURE)
        path = directory / "formalization.yaml"
        path.write_text(
            path.read_text(encoding="utf-8").replace(
                "    Fixture node.", '    Fixture <script>alert("x")</script> & "quoted".'),
            encoding="utf-8")
        page = ieantn.render_graph_page(ieantn.load_nodes())
        self.assertNotIn("<script>alert", page)
