from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def test_artifact_infrastructure_status_verifier_passes():
    result = subprocess.run(
        [sys.executable, "scripts/check_artifact_infrastructure_status.py"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "ARTIFACT_INFRASTRUCTURE_STATUS: PASS" in result.stdout

def test_artifact_infrastructure_status_does_not_claim_theorem_closure():
    text = (ROOT / "docs/status/ARTIFACT_INFRASTRUCTURE_STATUS_2026_04_27.md").read_text(encoding="utf-8")
    forbidden = [
        "solves the theorem",
        "final theorem proved",
        "peer reviewed",
        "externally validated",
        "unconditional mathematical closure",
    ]
    lowered = text.lower()
    for phrase in forbidden:
        assert phrase not in lowered
