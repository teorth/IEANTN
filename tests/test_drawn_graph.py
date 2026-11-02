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
class TestHoverText(FixtureRepo):
    """A box says what it claims, not only what it is called.

    The prose is already written -- a conclusion's docstring is where its informal statement
    lives, and a node's `project.description` is the paragraph the Palomar metadata carries --
    so the drawing can show it for the price of putting it in a `<title>`.
    """

    def write_docstring(self, node_id: str, cid: str, doc: str) -> None:
        directory = self.root / "IEANTN" / "Nodes" / node_id.replace(".", "/")
        (directory / "Conclusions.lean").write_text(
            f"import IEANTN.Vocabulary\n\nnamespace {node_id}\n\n"
            f"/-- {doc} -/\ndef {cid} : Prop := True\n\nend {node_id}\n",
            encoding="utf-8")

    def test_a_claim_carries_its_own_docstring(self) -> None:
        """Not the node's description: at this resolution a box is one conclusion, and the node's
        paragraph would repeat over every box of the node while describing none of them."""
        self.write_node("A.v1", LITERATURE)
        self.write_docstring("A.v1", "main", "**The claim.** Something true,\n\nand why.")
        page = ieantn.render_graph_page(ieantn.load_nodes())
        # Paragraphs stay on their own lines, which is how a formula on the line after its
        # lead-in should read, and the bold markers are gone.
        self.assertIn("The claim. Something true," + chr(10) + "and why.", page)

    def test_a_node_version_carries_its_description(self) -> None:
        self.write_node("A.v1", LITERATURE)
        page = ieantn.render_graph_page(ieantn.load_nodes())
        self.assertIn("Fixture node.", page)

    def test_a_box_that_stands_alone_gets_the_same_hovertext(self) -> None:
        """It is listed rather than drawn, which must not cost it its summary."""
        self.write_node("A.v1", LITERATURE)
        self.write_docstring("A.v1", "main", "Only in the list.")
        page = ieantn.render_graph_page(ieantn.load_nodes())
        self.assertIn("Stands alone", page)
        self.assertRegex(page, r'<li class="box" data-key="A\.v1\.main".*?title="[^"]*'
                               r'Only in the list\.')


class TestSummaryText(FixtureRepo):
    def test_it_takes_whole_paragraphs_not_the_first_line(self) -> None:
        """A conclusion docstring tends to open with a bolded name and run the statement onto the
        next paragraph, so stopping at the first blank line shows a fragment ending in a comma."""
        folded = ieantn.summary_text("**Chebyshev's upper bound.** For every x >= 30,"
                                     "\n\npsi(x) <= 6 a x / 5.")
        self.assertIn("For every x >= 30,", folded)
        self.assertIn("psi(x) <= 6 a x / 5.", folded)

    def test_a_paragraph_that_does_not_fit_is_shortened_not_dropped(self) -> None:
        """Dropping it cost `KadiriLumley.v1.table_2` everything it had to say."""
        folded = ieantn.summary_text("Short opener." + "\n\n" + "word " * 400)
        self.assertIn("Short opener.", folded)
        self.assertIn("word", folded.split("Short opener.")[1])
        self.assertTrue(folded.endswith("..."))

    def test_it_is_wrapped_because_a_tooltip_is_not_reliably_wrapped(self) -> None:
        folded = ieantn.summary_text("word " * 200)
        self.assertTrue(all(len(line) <= 78 for line in folded.splitlines()), folded)

    def test_bold_markers_go_and_backticks_stay(self) -> None:
        """Nobody is rendering the Markdown, but a backtick still says `psi` is a Lean name."""
        folded = ieantn.summary_text("**Bold.** The `psi` function.")
        self.assertNotIn("**", folded)
        self.assertIn("`psi`", folded)

    def test_it_survives_an_empty_docstring(self) -> None:
        self.assertEqual(ieantn.summary_text(""), "")
        self.assertEqual(ieantn.summary_text(None), "")
