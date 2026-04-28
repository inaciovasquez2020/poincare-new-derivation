#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs/status/BDE7_SCOPE_LOCK.md"
EXPOSURE = ROOT / "docs/math/DEGREE_3_EXPOSURE_LEMMA.md"

REQUIRED_DOC = [
    "Status: Conditional finite-certificate scope lock.",
    "N=7",
    "\\mathrm{BDE}(7)",
    "|V(T)|\\le 7",
    "This is not a global theorem.",
    "This is not a proof of the Poincare conjecture.",
    "This does not revive the false global non-increasing Degree-3 Exposure Lemma.",
    "The \\(600\\)-cell obstruction has \\(|V|=120\\)",
    "Any extension from \\(\\mathrm{BDE}(7)\\) to \\(\\mathrm{BDE}(N)\\) for larger \\(N\\) requires a new explicit finite certificate.",
    "Any global replacement requires a barrier-descent theorem allowing temporary increases of \\(\\Phi\\).",
    "No theorem-level Poincare closure follows from this file.",
]

REQUIRED_EXPOSURE = [
    "Status: Global formulation false.",
    "\\mathrm{BDE}(N)",
    "finite certificate target, not a global theorem",
    "barrier-descent",
    "No theorem-level Poincaré closure follows from this file.",
]

FORBIDDEN_DOC = [
    "Status: Proven",
    "Poincare conjecture is proved",
    "Poincaré conjecture is proved",
    "global theorem proved",
    "BDE(N) proved for all N",
]

def compact(s: str) -> str:
    return "".join(s.split())

def require(path: Path, needles: list[str]) -> list[str]:
    text = path.read_text(encoding="utf-8")
    c = compact(text)
    return [n for n in needles if n not in text and compact(n) not in c]

def main() -> int:
    if not DOC.exists():
        print("FAIL: missing docs/status/BDE7_SCOPE_LOCK.md", file=sys.stderr)
        return 1
    if not EXPOSURE.exists():
        print("FAIL: missing docs/math/DEGREE_3_EXPOSURE_LEMMA.md", file=sys.stderr)
        return 1

    missing = require(DOC, REQUIRED_DOC) + require(EXPOSURE, REQUIRED_EXPOSURE)
    if missing:
        print("FAIL: missing required strings:", file=sys.stderr)
        for item in missing:
            print(f"- {item}", file=sys.stderr)
        return 1

    text = DOC.read_text(encoding="utf-8")
    bad = [s for s in FORBIDDEN_DOC if s in text]
    if bad:
        print("FAIL: forbidden overclaim strings:", file=sys.stderr)
        for item in bad:
            print(f"- {item}", file=sys.stderr)
        return 1

    print({
        "status": "PASS",
        "bounded_frontier": "BDE(7)",
        "global_degree3_exposure": "false",
        "poincare_theorem_level_closure": False,
    })
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
