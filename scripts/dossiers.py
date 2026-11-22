#!/usr/bin/env python3
"""Validate optional source dossiers.

A dossier records a reading of one declaration against a pinned edition of a paper: where the
statement sits, the domain it assumes, which way a displayed numeral was rounded, and the
divergences a reviewer has already written down. The checks below are about the record's shape.
They do not decide that the statement is true, and they do not compare it with a paper that is
not already copied into the dossier.
"""

from __future__ import annotations

import re
from fractions import Fraction

SCHEMA = "ieantn-source-dossier/1"
NODE_ID = re.compile(r"^[A-Za-z][A-Za-z0-9_]*\.v[1-9][0-9]*$")
DECLARATION_ID = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
PAGE_RANGE = re.compile(r"^\d+\s*-\s*\d+$")
PIN_YEAR = re.compile(r"\((\d{4})\)")
DISPLAY = re.compile(r"-?\d+(?:\.\d+)?")
EXACT = re.compile(r"-?\d+(?:/-?\d+)?")
ROUNDING = {"exact", "up", "down", "toward-zero", "away-from-zero"}
EDITION_KEYS = {"pin", "year", "pages"}
QUANTITY_KEYS = {"display", "exact", "name"}
DECLARATION_KEYS = {
    "key", "edition", "locator", "domain", "rounding", "quantities", "divergences",
}


def _display(text: object) -> Fraction | None:
    if not isinstance(text, str) or DISPLAY.fullmatch(text) is None:
        return None
    return Fraction(text)


def _exact(text: object) -> Fraction | None:
    if not isinstance(text, str) or EXACT.fullmatch(text) is None:
        return None
    if "/" not in text:
        return Fraction(int(text), 1)
    numerator, denominator = text.split("/", 1)
    if int(denominator) == 0:
        return None
    return Fraction(int(numerator), int(denominator))


def _quantity_error(display: Fraction, exact: Fraction, rounding: str, shown: str, raw: str) -> str | None:
    """How a displayed numeral has to sit relative to the exact rational."""
    if rounding == "exact":
        if display != exact:
            return f"display {shown} is not the exact rational {raw}"
        return None
    if rounding == "up":
        if not display > exact:
            return f"rounding up requires display {shown} to be strictly greater than exact {raw}"
        return None
    if rounding == "down":
        if not display < exact:
            return f"rounding down requires display {shown} to be strictly less than exact {raw}"
        return None
    if rounding == "toward-zero":
        if abs(display) < abs(exact) and display * exact >= 0:
            return None
        return f"rounding toward zero requires display {shown} to be strictly closer to zero than exact {raw}"
    if rounding == "away-from-zero":
        if abs(display) > abs(exact) and display * exact > 0:
            return None
        return (
            f"rounding away from zero requires display {shown} to be strictly farther from zero "
            f"than exact {raw}"
        )
    return f"unknown rounding direction {rounding!r}"


def _edition_errors(edition: object) -> list[str]:
    if not isinstance(edition, dict):
        return ["edition must be a mapping with pin, year, and pages"]
    errors: list[str] = []
    extra = sorted(set(edition) - EDITION_KEYS)
    if extra:
        errors.append(f"edition has unexpected keys: {', '.join(extra)}")
    pin = edition.get("pin")
    year = edition.get("year")
    pages = edition.get("pages")
    if not isinstance(pin, str) or not pin.strip():
        errors.append("edition.pin is required")
    if isinstance(year, bool) or not isinstance(year, int):
        errors.append("edition.year must be an integer")
    if not isinstance(pages, str) or PAGE_RANGE.fullmatch(pages) is None:
        errors.append("edition.pages must be a page range like 64-94")
    if isinstance(pin, str) and isinstance(year, int) and not isinstance(year, bool):
        cited = {int(match) for match in PIN_YEAR.findall(pin)}
        if cited != {year}:
            shown = ", ".join(str(item) for item in sorted(cited)) or "none"
            errors.append(
                f"edition mismatch: pin cites year {shown} but year is {year}"
            )
    if isinstance(pin, str) and isinstance(pages, str) and PAGE_RANGE.fullmatch(pages) and pages not in pin:
        errors.append(f"edition mismatch: pages {pages} are not in the pin")
    return errors


def _declaration_errors(entry: object, node: str, index: int) -> list[str]:
    where = f"declarations[{index}]"
    if not isinstance(entry, dict):
        return [f"{where} must be a mapping"]
    errors: list[str] = []
    extra = sorted(set(entry) - DECLARATION_KEYS)
    if extra:
        errors.append(f"{where} has unexpected keys: {', '.join(extra)}")
    key = entry.get("key")
    prefix = f"{node}."
    if not isinstance(key, str) or not key.startswith(prefix) or DECLARATION_ID.fullmatch(key[len(prefix):]) is None:
        errors.append(f"{where}.key must be {node}.<declaration>")
    if "edition" not in entry:
        errors.append(f"{where}.edition is required")
    else:
        errors += [f"{where}.{message}" for message in _edition_errors(entry.get("edition"))]
    locator = entry.get("locator")
    if "locator" not in entry or not isinstance(locator, str) or not locator.strip():
        errors.append(f"{where}.locator is required")
    domain = entry.get("domain")
    if not isinstance(domain, str) or not domain.strip():
        errors.append(f"{where}.domain is required")
    rounding = entry.get("rounding")
    if rounding not in ROUNDING:
        errors.append(
            f"{where}.rounding must be one of {', '.join(sorted(ROUNDING))}"
        )
    quantities = entry.get("quantities")
    if not isinstance(quantities, list):
        errors.append(f"{where}.quantities must be a list")
    elif isinstance(rounding, str) and rounding in ROUNDING:
        for offset, quantity in enumerate(quantities):
            label = f"{where}.quantities[{offset}]"
            if not isinstance(quantity, dict):
                errors.append(f"{label} must be a mapping")
                continue
            unexpected = sorted(set(quantity) - QUANTITY_KEYS)
            if unexpected:
                errors.append(f"{label} has unexpected keys: {', '.join(unexpected)}")
            shown = quantity.get("display")
            raw = quantity.get("exact")
            parsed_display = _display(shown)
            parsed_exact = _exact(raw)
            if parsed_display is None:
                errors.append(f"{label}.display must be a decimal numeral")
            if parsed_exact is None:
                errors.append(f"{label}.exact must be an integer or a rational n/d")
            name = quantity.get("name")
            if "name" in quantity and (not isinstance(name, str) or not name.strip()):
                errors.append(f"{label}.name must be a non-empty string when present")
            if parsed_display is not None and parsed_exact is not None and isinstance(shown, str) and isinstance(raw, str):
                message = _quantity_error(parsed_display, parsed_exact, rounding, shown, raw)
                if message:
                    errors.append(f"{label}: {message}")
    divergences = entry.get("divergences")
    if not isinstance(divergences, list):
        errors.append(f"{where}.divergences is required and must be a list")
    else:
        for offset, note in enumerate(divergences):
            if not isinstance(note, str) or not note.strip():
                errors.append(f"{where}.divergences[{offset}] must be a non-empty string")
    return errors


def validate_dossier(data: object, node_id: str | None = None) -> list[str]:
    """Errors in one dossier. An empty list means the shape checks passed."""
    if not isinstance(data, dict):
        return ["dossier must be a mapping"]
    errors: list[str] = []
    if data.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA}")
    node = data.get("node")
    if not isinstance(node, str) or NODE_ID.fullmatch(node) is None:
        errors.append("node must be a node id such as RosserSchoenfeld1962.v1")
        node = node if isinstance(node, str) else ""
    elif node_id is not None and node != node_id:
        errors.append(f"node is {node} but the file is in {node_id}")
    declarations = data.get("declarations")
    if not isinstance(declarations, list) or not declarations:
        errors.append("declarations must be a non-empty list")
    else:
        for index, entry in enumerate(declarations):
            errors += _declaration_errors(entry, node, index)
    allowed = {"schema", "node", "declarations"}
    extra = sorted(set(data) - allowed)
    if extra:
        errors.append(f"unexpected keys: {', '.join(extra)}")
    return errors
