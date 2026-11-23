"""Shape checks for source dossiers. The failure cases are fixtures, not node files."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest

import yaml

_SCRIPTS = pathlib.Path(__file__).resolve().parent.parent / "scripts"
_SPEC = importlib.util.spec_from_file_location("dossiers", _SCRIPTS / "dossiers.py")
assert _SPEC and _SPEC.loader
dossiers = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(dossiers)

ROOT = pathlib.Path(__file__).resolve().parent.parent


def sample() -> dict:
    """One well-shaped declaration. The numerals are the printed 1.03883 bound, as a fixture."""
    return {
        "schema": dossiers.SCHEMA,
        "node": "RosserSchoenfeld1962.v1",
        "declarations": [
            {
                "key": "RosserSchoenfeld1962.v1.equation_3_35",
                "edition": {
                    "pin": "Illinois Journal of Mathematics 6(1) (1962), 64-94",
                    "year": 1962,
                    "pages": "64-94",
                },
                "locator": "Theorem 12, equation (3.35), p. 71",
                "domain": "every real x > 0",
                "rounding": "exact",
                "quantities": [{"display": "1.03883", "exact": "103883/100000"}],
                "divergences": [],
            }
        ],
    }


class TestDossiers(unittest.TestCase):
    def test_missing_locator(self) -> None:
        data = sample()
        del data["declarations"][0]["locator"]
        errors = dossiers.validate_dossier(data)
        self.assertTrue(any(error.endswith("locator is required") for error in errors))
        data = sample()
        data["declarations"][0]["locator"] = "   "
        errors = dossiers.validate_dossier(data)
        self.assertTrue(any("locator is required" in error for error in errors))

    def test_edition_mismatch_shape(self) -> None:
        data = sample()
        data["declarations"][0]["edition"]["year"] = 1975
        errors = dossiers.validate_dossier(data)
        self.assertTrue(any(error.startswith("declarations[0].edition mismatch:") for error in errors))
        self.assertTrue(any("1975" in error and "1962" in error for error in errors))

        data = sample()
        data["declarations"][0]["edition"]["pages"] = "Theorem 12"
        errors = dossiers.validate_dossier(data)
        self.assertTrue(any("edition.pages must be a page range" in error for error in errors))

        data = sample()
        data["declarations"][0]["edition"] = "Illinois J. Math. 1962"
        errors = dossiers.validate_dossier(data)
        self.assertTrue(any("edition must be a mapping" in error for error in errors))

    def test_exact_rational_versus_display(self) -> None:
        self.assertEqual(dossiers.validate_dossier(sample()), [])
        data = sample()
        data["declarations"][0]["quantities"][0]["exact"] = "103882/100000"
        errors = dossiers.validate_dossier(data)
        self.assertTrue(any(
            "display 1.03883 is not the exact rational 103882/100000" in error for error in errors
        ))
        # A fixture for the direction check. The repository's comment on this constant writes
        # 10.319317 with an ellipsis, so that longer expansion is not recorded as a source pin.
        data = sample()
        data["declarations"][0]["rounding"] = "up"
        data["declarations"][0]["quantities"][0]["display"] = "10.3194"
        data["declarations"][0]["quantities"][0]["exact"] = "10319317/1000000"
        self.assertEqual(dossiers.validate_dossier(data), [])
        data = copy.deepcopy(data)
        data["declarations"][0]["quantities"][0]["exact"] = "103194/10000"
        errors = dossiers.validate_dossier(data)
        self.assertTrue(any("rounding up requires display 10.3194" in error for error in errors))

    def test_recorded_dossiers_use_locators_already_in_the_repo(self) -> None:
        paths = [
            ROOT / "IEANTN/Nodes/RosserSchoenfeld1962/v1/dossier.yaml",
            ROOT / "IEANTN/Nodes/Trudgian2011/v1/dossier.yaml",
        ]
        for path in paths:
            data = yaml.safe_load(path.read_text(encoding="utf-8"))
            node = path.parent.relative_to(ROOT / "IEANTN/Nodes").as_posix().replace("/", ".")
            self.assertEqual(dossiers.validate_dossier(data, node), [], path)


if __name__ == "__main__":
    unittest.main()
