from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

required_files = [
    ROOT / "docs/status/ARTIFACT_INFRASTRUCTURE_STATUS_2026_04_27.md",
]

required_phrases = {
    ROOT / "docs/status/ARTIFACT_INFRASTRUCTURE_STATUS_2026_04_27.md": [
        "Status: Infrastructure Audit",
        "Mathematical Status: Unchanged",
        "External Validation Status: Unchanged",
        "does not assert theorem-level completion",
        "Stop rule",
    ],
}

missing = []

for path in required_files:
    if not path.exists():
        missing.append(f"missing file: {path.relative_to(ROOT)}")

for path, phrases in required_phrases.items():
    if path.exists():
        text = path.read_text(encoding="utf-8")
        for phrase in phrases:
            if phrase not in text:
                missing.append(f"missing phrase in {path.relative_to(ROOT)}: {phrase}")

if missing:
    print("ARTIFACT_INFRASTRUCTURE_STATUS: FAIL")
    for item in missing:
        print(f"- {item}")
    sys.exit(1)

print("ARTIFACT_INFRASTRUCTURE_STATUS: PASS")
