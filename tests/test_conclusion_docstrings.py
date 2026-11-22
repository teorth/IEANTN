#!/usr/bin/env python3
"""The informal statement has to mention the hypotheses the declaration asks for.

Issue 183: the numerical-bound docstring omitted `0 < h`, `x₀ ≤ x` and `0 < x`,
and `IsBandLimited` called `φ` band-limited when the declaration says `φ` is
supported on `[-1, 1]` and the Fourier transform is the one that decays.
"""
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class TestConclusionDocstrings(unittest.TestCase):
    def test_numerical_bound_names_its_hypotheses(self) -> None:
        text = (ROOT / "IEANTN/Nodes/PrimeInterval/v1/Conclusions.lean").read_text(encoding="utf-8")
        start = text.index("The numerical-bound route:")
        paragraph = text[start:text.index("-/", start)]
        for piece in ("0 < h", "x₀ ≤ x", "0 < x", "(2x + h) * ε < h"):
            self.assertIn(piece, paragraph)
        self.assertNotIn("0 < x₀ ≤ x", paragraph)

    def test_band_limited_is_the_transform_not_phi(self) -> None:
        text = (ROOT / "IEANTN/Nodes/CH2/v2/Conclusions.lean").read_text(encoding="utf-8")
        start = text.index("def IsBandLimited")
        docstring = text[text.rindex("/--", 0, start):start]
        self.assertIn("supported on", docstring)
        self.assertNotIn("band-limited to", docstring)
        self.assertIn("Fourier transform", docstring)
