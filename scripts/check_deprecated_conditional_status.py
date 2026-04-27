#!/usr/bin/env python3
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
STATUS_DOC = ROOT / "docs/status/DEPRECATED_CONDITIONAL_STATUS_2026_04_27.md"
FORMAL_DOC = ROOT / "docs/status/FORMAL_STATUS_2026_04_27.md"
README = ROOT / "README.md"

PATTERNS = {
    "axiom": re.compile(r"^\s*axiom\s+"),
    "admit": re.compile(r"\badmit\b"),
    "sorry": re.compile(r"\bsorry\b"),
}

def lean_files():
    return [
        p for p in ROOT.rglob("*.lean")
        if ".lake" not in p.parts and ".git" not in p.parts
    ]

def counts() -> dict[str, int]:
    out = {k: 0 for k in PATTERNS}
    for p in lean_files():
        for line in p.read_text(encoding="utf-8", errors="ignore").splitlines():
            for name, rx in PATTERNS.items():
                if rx.search(line):
                    out[name] += 1
    return out

def main() -> int:
    if not STATUS_DOC.exists():
        print(f"missing status document: {STATUS_DOC.relative_to(ROOT)}")
        return 1

    if not FORMAL_DOC.exists():
        print(f"missing formal status document: {FORMAL_DOC.relative_to(ROOT)}")
        return 1

    if not README.exists():
        print("missing README.md")
        return 1

    text = STATUS_DOC.read_text(encoding="utf-8", errors="ignore")
    formal_text = FORMAL_DOC.read_text(encoding="utf-8", errors="ignore")
    readme_text = README.read_text(encoding="utf-8", errors="ignore")
    c = counts()

    required = [
        "Status: Deprecated / Conditional Sketch",
        "This repository is not a proof of the Poincare conjecture.",
        "It contains sorries, axioms, or admitted obligations",
        "If `axiom + admit + sorry > 0`, no Poincare-proof claim is allowed.",
        "Axiom count: " + str(c["axiom"]),
        "Admit count: " + str(c["admit"]),
        "Sorry count: " + str(c["sorry"]),
    ]

    missing = [s for s in required if s not in text]
    if missing:
        print("deprecated conditional status check failed")
        for s in missing:
            print(f"missing: {s}")
        return 1

    formal_required = [
        "Status: Deprecated / Conditional Sketch",
        "The repository builds, but build success is not theorem verification.",
        "`axiom` is a trusted assumption, not a proof.",
        "`sorry` is a proof hole.",
        "If `axiom + admit + sorry > 0`, no Poincare-proof claim is allowed.",
    ]
    formal_missing = [s for s in formal_required if s not in formal_text]
    if formal_missing:
        print("Poincare formal-status boundary check failed")
        for s in formal_missing:
            print(f"missing: {s}")
        return 1

    readme_required = [
        "## Formal Status",
        "Status: Deprecated / Conditional Sketch",
        "`axiom` is a trusted assumption, not a proof.",
        "`sorry` is a proof hole.",
        "Conditional inventory: `docs/status/DEPRECATED_CONDITIONAL_STATUS_2026_04_27.md`",
    ]
    readme_missing = [s for s in readme_required if s not in readme_text]
    if readme_missing:
        print("README formal-status block check failed")
        for s in readme_missing:
            print(f"missing: {s}")
        return 1

    print({
        "status": "PASS",
        "classification": "Deprecated / Conditional Sketch",
        "axiom_count": c["axiom"],
        "admit_count": c["admit"],
        "sorry_count": c["sorry"],
        "status_doc": str(STATUS_DOC.relative_to(ROOT)),
        "formal_status_doc": str(FORMAL_DOC.relative_to(ROOT)),
        "readme_status_block": "PASS",
    })
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
