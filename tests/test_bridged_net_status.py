#!/usr/bin/env python3
"""A bridged conclusion inherits the status of what its bridge rests on.

`status` used to report every `bridged` conclusion as `-`, the same marker as a bare citation.
That understated them badly. A bridge is an ordinary Lean theorem under `IEANTN/Bridges/`, inside
the core build, so it is `sorry`-free and re-checked on every push; what it proves is exactly as
good as what it consumes. `ChebyshevNumerics.v1.psi_le_below_11723` rests on a Comparator receipt
one hop away and shared a line with claims nobody had checked at all.

The weakest source wins, because a bridge can discharge nothing it was not given.

The invariant guarded in `TestImportsAreNotPropagated` is the subtle one: a conclusion's declared
*imports* must NOT drag its light down, however unproved they are. A challenge states an
implication and the implication is what Comparator verified -- `assess` is deliberately built that
way, and propagating imports here would grade most of the network unverified.
"""
from __future__ import annotations

import contextlib
import io
import json
import unittest
import unittest.mock

from test_ieantn import (LITERATURE, REFUTED, FixtureRepo, bridged, bridged_from, ieantn,
                         importing)

DIGEST = "digest-as-built"


class _Bridges(FixtureRepo):
    def verified(self, node_id: str, *, conclusions: str | None = None) -> str:
        """A node designating `lean-comparator`, with a receipt that grades green."""
        body = conclusions if conclusions is not None else LITERATURE
        # The fixtures spell their placeholder kind differently -- `literature` in LITERATURE,
        # `none-yet` in `importing` -- so swap whichever is there rather than assuming one.
        for placeholder in ("kind: literature", "kind: none-yet"):
            body = body.replace(placeholder, "kind: lean-comparator")
        self.write_node(node_id, body)
        key = f"{node_id}.main"
        family, version = node_id.rsplit(".", 1)
        (self.root / "IEANTN" / "Nodes" / family / version / "fingerprints.json").write_text(
            json.dumps({key: DIGEST}), encoding="utf-8")
        (self.root / "receipts").mkdir(exist_ok=True)
        (self.root / "receipts" / f"{key}.json").write_text(json.dumps({
            "conclusion": key,
            "statement": {key: DIGEST},
            "environment": ieantn.current_environment(),
        }), encoding="utf-8")
        return key

    def light(self, key: str) -> tuple[str, str]:
        nodes = ieantn.load_nodes()
        index = {
            f"{node_id}.{c.get('id')}": c
            for node_id, node in nodes.items()
            for c in ieantn.conclusions_of(node)
        }
        fingerprints = {name: DIGEST for name in index}
        return ieantn.net_light(key, index, fingerprints, {})


class TestABridgeInheritsAVerifiedSource(_Bridges):
    def test_a_bridge_from_a_verified_conclusion_is_green(self) -> None:
        """The regression: this used to be `-`, beside the unchecked citations."""
        self.verified("Src.v1")
        self.write_node("A.v1", bridged("Src.v1.main"))
        light, detail = self.light("A.v1.main")
        self.assertEqual(light, "green")
        self.assertIn("Src.v1.main", detail)
        self.assertIn("core build", detail)

    def test_status_prints_it(self) -> None:
        self.verified("Src.v1")
        self.write_node("A.v1", bridged("Src.v1.main"))
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed), unittest.mock.patch.object(
            ieantn, "compute_fingerprints",
            return_value={"Src.v1.main": DIGEST, "A.v1.main": DIGEST},
        ):
            ieantn.status()
        out = printed.getvalue()
        self.assertIn("green   A.v1.main", out)
        self.assertNotIn("-       A.v1.main", out)

    def test_a_chain_of_bridges_still_reaches_the_receipt(self) -> None:
        """B bridges onto A, A onto a verified source. Both are green."""
        self.verified("Src.v1")
        self.write_node("A.v1", bridged("Src.v1.main"))
        self.write_node("B.v1", bridged("A.v1.main"))
        self.assertEqual(self.light("A.v1.main")[0], "green")
        self.assertEqual(self.light("B.v1.main")[0], "green")


class TestTheWeakestSourceWins(_Bridges):
    def test_a_bridge_from_a_citation_stays_unverified(self) -> None:
        self.write_node("Src.v1", LITERATURE)
        self.write_node("A.v1", bridged("Src.v1.main"))
        light, detail = self.light("A.v1.main")
        self.assertEqual(light, "-")
        self.assertIn("Src.v1.main", detail)
        self.assertIn("designated `literature`", detail)

    def test_a_bridge_from_a_refuted_conclusion_is_refuted(self) -> None:
        """Inheriting the worst case matters most here: the source is false."""
        self.write_node("Src.v1", REFUTED)
        self.write_node("A.v1", bridged("Src.v1.main"))
        light, detail = self.light("A.v1.main")
        self.assertEqual(light, "refuted")
        self.assertIn("Src.v1.main", detail)

    def test_a_multi_source_bridge_takes_the_weakest(self) -> None:
        self.verified("Good.v1")
        self.write_node("Weak.v1", LITERATURE)
        self.write_node("A.v1", bridged_from(["Good.v1.main", "Weak.v1.main"]))
        light, detail = self.light("A.v1.main")
        self.assertEqual(light, "-")
        self.assertIn("Weak.v1.main", detail)
        self.assertNotIn("Good.v1.main", detail)

    def test_a_missing_receipt_propagates_as_broken(self) -> None:
        self.write_node("Src.v1", LITERATURE.replace("kind: literature", "kind: lean-comparator"))
        self.write_node("A.v1", bridged("Src.v1.main"))
        light, _ = self.light("A.v1.main")
        self.assertEqual(light, "BROKEN")


class TestImportsAreNotPropagated(_Bridges):
    """The architectural invariant: a challenge states an implication.

    `assess` does not downgrade a green receipt because a hypothesis is unproved, and this
    propagation must not either. Getting it wrong would turn most of the network red, since many
    receipts are green precisely because the statement is conditional.
    """

    def test_a_verified_conclusion_with_an_unproved_import_stays_green(self) -> None:
        self.write_node("Leaf.v1", LITERATURE)
        key = self.verified("A.v1", conclusions=importing("Leaf.v1"))
        # The receipt has to record the hypothesis, or `assess` rightly calls it BROKEN.
        receipt = self.root / "receipts" / f"{key}.json"
        payload = json.loads(receipt.read_text(encoding="utf-8"))
        payload["statement"]["Leaf.v1.main"] = DIGEST
        receipt.write_text(json.dumps(payload), encoding="utf-8")
        self.assertEqual(self.light(key)[0], "green")


class TestMalformedNetworks(_Bridges):
    def test_a_bridge_cycle_does_not_recurse_forever(self) -> None:
        """`check` refuses cycles; `status` must still be able to report one."""
        self.write_node("A.v1", bridged("B.v1.main"))
        self.write_node("B.v1", bridged("A.v1.main"))
        light, detail = self.light("A.v1.main")
        self.assertEqual(light, "-")
        self.assertIn("cycle", detail)

    def test_a_bridge_onto_a_conclusion_that_does_not_exist(self) -> None:
        self.write_node("A.v1", bridged("Nowhere.v1.main"))
        light, detail = self.light("A.v1.main")
        self.assertEqual(light, "-")
        self.assertIn("not a conclusion", detail)


class TestTheCommittedNetwork(unittest.TestCase):
    def test_every_bridged_conclusion_matches_its_weakest_source(self) -> None:
        """A property, against the real network rather than a fixture."""
        nodes = ieantn.load_nodes()
        index = {
            f"{node_id}.{c.get('id')}": c
            for node_id, node in nodes.items()
            for c in ieantn.conclusions_of(node)
        }
        fingerprints = ieantn.compute_fingerprints()
        cache: dict[str, tuple[str, str]] = {}
        bridged_keys = [k for k, c in index.items()
                        if ieantn.designated_kind(c) == "bridged" and not c.get("refuted")]
        self.assertTrue(bridged_keys, "the network has no bridged conclusion to check")
        for key in sorted(bridged_keys):
            sources = ieantn.bridge_sources(ieantn.designated_of(index[key]) or {})
            worst = max(
                (ieantn.net_light(s, index, fingerprints, cache)[0] for s in sources),
                key=lambda light: ieantn.LIGHT_STRENGTH[light],
            )
            with self.subTest(conclusion=key):
                self.assertEqual(ieantn.net_light(key, index, fingerprints, cache)[0], worst)


if __name__ == "__main__":
    unittest.main()
