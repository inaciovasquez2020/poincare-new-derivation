import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_perelman_pl_conditional_closure_verifier():
    subprocess.run(
        ["python3", "tools/verify_perelman_pl_conditional_closure.py"],
        cwd=ROOT,
        check=True,
    )


def test_perelman_pl_lean_surface_has_no_false_closure_language():
    text = (ROOT / "lean/Poincare/PerelmanPL.lean").read_text()
    assert "CONDITIONAL_EXTERNAL_THEOREM_ONLY" in text
    assert "theorem-complete" not in text
    assert "solves" not in text
    assert "solved" not in text


def test_contradiction_quarantine_records_identity_obstruction():
    text = (ROOT / "lean/Poincare/ContradictionQuarantine.lean").read_text()
    assert "applyMoveImpl_identity" in text
    assert "current_applyMoveImpl_blocks_strict_descent" in text
    assert "rfl" in text
