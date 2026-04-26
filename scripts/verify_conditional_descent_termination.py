#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from conditional_descent_termination import verify_descent_chain


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> int:
    doc = ROOT / "docs/math/CONDITIONAL_DESCENT_TERMINATION_THEOREM.md"
    status = ROOT / "STATUS.md"
    source = ROOT / "src/conditional_descent_termination.py"
    require(doc.exists(), "missing theorem document")
    require(status.exists(), "missing STATUS.md")
    require(source.exists(), "missing source file")
    doc_text = doc.read_text(encoding="utf-8")
    status_text = status.read_text(encoding="utf-8")
    for literal in [
        "Status: CLOSED repository-scope conditional theorem.",
        "Theorem ID: PND-CDT-1.",
        "x R y  implies  h(y) < h(x).",
        "no infinite `R`-chain exists",
        "This does not prove the Poincare conjecture.",
        "The remaining mathematical frontier is the admissibility theorem",
    ]:
        require(literal in doc_text, f"missing theorem literal: {literal}")
    for literal in [
        "Conditional descent termination theorem: CLOSED",
        "No repository-level claim of a Poincare proof.",
        "No repository-level claim of move-system completeness.",
        "Remaining frontier",
    ]:
        require(literal in status_text, f"missing status literal: {literal}")
    cert = verify_descent_chain([7, 5, 3, 2, 0])
    require(cert.theorem_id == "PND-CDT-1", "wrong theorem id")
    require(cert.status == "PASS", "certificate did not pass")
    require(cert.strictly_descending is True, "chain is not strictly descending")
    require(cert.bound_respected is True, "length bound failed")
    require(cert.step_count <= cert.initial_height, "step count exceeds height bound")
    print(json.dumps(cert.__dict__, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
