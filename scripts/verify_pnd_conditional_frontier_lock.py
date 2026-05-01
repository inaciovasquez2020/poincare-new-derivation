#!/usr/bin/env python3
"""Verify the PND Conditional Frontier Lock status document."""

from __future__ import annotations

import re
import sys
from pathlib import Path

LOCK_PATH = Path("docs/status/PND_CONDITIONAL_FRONTIER_LOCK_2026_05_01.md")

REQUIRED_STRINGS = [
    "# PND Conditional Frontier Lock — 2026-05-01",
    "Conditional.",
    "Remaining sorry and axiom objects are frontier obligations, not proofs.",
    "Build success verifies artifact integrity only.",
    "No unconditional Poincaré theorem is asserted.",
    "This document does not assert theorem-level closure.",
    "Total sorry: 43",
    "Total admit: 0",
    "Total axiom: 31",
    "Total holes: 74",
    "## Weakest remaining mathematical obligations",
    "- Constructive move realization.",
    "- Unit Phi-drop from move realization.",
    "- Terminal zero recognition.",
    "- Regge holonomy axioms.",
    "- Canonical code / Oblivion proof holes.",
]

REQUIRED_ROWS = [
    "| `lean/Poincare/FinalConstructive.lean` | 18 | 0 | 0 | 18 |",
    "| `lean/Oblivion/CanonicalCodes.lean` | 16 | 0 | 0 | 16 |",
    "| `lean/Regge/HolonomyMatrixModel.lean` | 0 | 0 | 11 | 11 |",
    "| `Poincare/GreedyDescent.lean` | 5 | 0 | 0 | 5 |",
    "| `lean/Regge/ReggeComplete.lean` | 2 | 0 | 3 | 5 |",
    "| `lean/Regge/ReggeMathComplete.lean` | 0 | 0 | 5 | 5 |",
    "| `lean/Regge/Core.lean` | 0 | 0 | 2 | 2 |",
    "| `lean/Regge/HolonomyDerived.lean` | 0 | 0 | 2 | 2 |",
    "| `lean/Regge/Pachner.lean` | 0 | 0 | 2 | 2 |",
    "| `Poincare/Foundations.lean` | 0 | 0 | 1 | 1 |",
    "| `lean/Cyclone/CycleBasisLift.lean` | 1 | 0 | 0 | 1 |",
    "| `lean/Oblivion/LASRStandalone.lean` | 1 | 0 | 0 | 1 |",
    "| `lean/Poincare/GreedySelectorCorrect.lean` | 0 | 0 | 1 | 1 |",
    "| `lean/Poincare/VertexDefectPhiPos.lean` | 0 | 0 | 1 | 1 |",
    "| `lean/Regge/FinalClosure.lean` | 0 | 0 | 1 | 1 |",
    "| `lean/Regge/Holonomy.lean` | 0 | 0 | 1 | 1 |",
    "| `lean/Regge/ReggeFinal.lean` | 0 | 0 | 1 | 1 |",
]

FORBIDDEN_PHRASES = [
    "Poincaré theorem is proved",
    "fully solved",
    "final proof complete",
    "axiom-free realization",
    "eliminate all sorry",
    "unconditional closure",
]

ALLOWED_STATUS_SAFE_SENTENCES = [
    "No unconditional Poincaré theorem is asserted.",
    "This document does not assert theorem-level closure.",
    "This document does not claim axiom-free realization.",
    "This document does not claim that all sorry occurrences have been eliminated.",
    "This document does not claim unconditional closure.",
]

TABLE_ROW_RE = re.compile(
    r"^\| `(?P<file>[^`]+)` \| (?P<sorry>\d+) \| (?P<admit>\d+) \| (?P<axiom>\d+) \| (?P<total>\d+) \|$",
    re.MULTILINE,
)


def _strip_allowed_sentences(text: str) -> str:
    scrubbed = text
    for sentence in ALLOWED_STATUS_SAFE_SENTENCES:
        scrubbed = scrubbed.replace(sentence, "")
    return scrubbed


def verify(lock_path: Path = LOCK_PATH) -> list[str]:
    errors: list[str] = []

    if not lock_path.is_file():
        return [f"Missing lock file: {lock_path}"]

    text = lock_path.read_text(encoding="utf-8")
    lines = text.splitlines()

    expected_header = [
        "# PND Conditional Frontier Lock — 2026-05-01",
        "",
        "Conditional.",
    ]
    if lines[:3] != expected_header:
        errors.append("Lock file must begin with the exact required header block.")

    for required in REQUIRED_STRINGS:
        if required not in text:
            errors.append(f"Missing required string: {required!r}")

    for row in REQUIRED_ROWS:
        if row not in text:
            errors.append(f"Missing required table row: {row!r}")

    parsed_rows = list(TABLE_ROW_RE.finditer(text))
    if len(parsed_rows) < len(REQUIRED_ROWS):
        errors.append(
            f"Expected at least {len(REQUIRED_ROWS)} parsed table rows; found {len(parsed_rows)}."
        )

    for match in parsed_rows:
        admit = int(match.group("admit"))
        if admit != 0:
            errors.append(
                f"Nonzero admit count in table row for {match.group('file')}: {admit}"
            )

    scrubbed = _strip_allowed_sentences(text)
    lowered = scrubbed.lower()
    for phrase in FORBIDDEN_PHRASES:
        if re.search(re.escape(phrase.lower()), lowered):
            errors.append(f"Forbidden unqualified phrase present: {phrase!r}")

    return errors


def main() -> int:
    errors = verify()
    if errors:
        print("PND Conditional Frontier Lock verification FAILED:")
        for error in errors:
            print(f"  - {error}")
        return 1

    print("PND Conditional Frontier Lock verification OK.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
