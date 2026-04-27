#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs/math/DEGREE_3_EXPOSURE_LEMMA.md"

REQUIRED = [
    "Status: Global formulation false.",
    "The previous global non-increasing exposure target is false.",
    "Counterexample: boundary of the 600-cell",
    "d(v)=20",
    "\\deg(e)=5",
    "1680>0",
    "d(v):20\\mapsto22",
    "=10>0",
    "=4>0",
    "the global non-increasing Degree-3 Exposure Lemma is false",
    "Invalid topological patch",
    "this antecedent is empty",
    "Corrected bounded frontier",
    "\\mathrm{BDE}(N)",
    "|V(T)|\\le N",
    "finite certificate target, not a global theorem",
    "If \\(N<120\\), the \\(600\\)-cell obstruction is outside the certified domain.",
    "Corrected global alternative",
    "barrier-descent",
    "No theorem-level Poincaré closure follows from this file.",
]

FORBIDDEN = [
    "Status: Proven",
    "Poincaré conjecture is proved",
    "global non-increasing Degree-3 Exposure Lemma is true",
]

def main() -> int:
    if not DOC.exists():
        print("FAIL: missing docs/math/DEGREE_3_EXPOSURE_LEMMA.md", file=sys.stderr)
        return 1

    text = DOC.read_text(encoding="utf-8")

    compact = "".join(text.split())
    missing = [s for s in REQUIRED if s not in text and "".join(s.split()) not in compact]
    if missing:
        print("FAIL: missing required strings:", file=sys.stderr)
        for s in missing:
            print(f"- {s}", file=sys.stderr)
        return 1

    bad = [s for s in FORBIDDEN if s in text]
    if bad:
        print("FAIL: forbidden overclaim strings:", file=sys.stderr)
        for s in bad:
            print(f"- {s}", file=sys.stderr)
        return 1

    print({
        "status": "PASS",
        "degree3_exposure_global_formulation": "false",
        "corrected_frontier": "bounded_BDE_N_or_global_barrier_descent",
        "poincare_theorem_level_closure": False,
    })
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
