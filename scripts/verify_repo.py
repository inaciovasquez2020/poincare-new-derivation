from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]

required = [
    "README.md",
    "STATUS.md",
    "FREEZE.md",
    "CITATION.cff",
]

missing = [p for p in required if not (root / p).exists()]
if missing:
    print({"valid": False, "missing": missing})
    sys.exit(1)

readme = (root / "README.md").read_text(encoding="utf-8", errors="ignore").lower()

checks = {
    "mentions_poincare": "poincare" in readme or "poincaré" in readme,
    "mentions_derivation_or_new": ("derivation" in readme) or ("new" in readme),
}

failed = [k for k, v in checks.items() if not v]
if failed:
    print({"valid": False, "failed_checks": failed})
    sys.exit(1)

print({"valid": True, "checked": required, "checks": checks})
