import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def test_bde7_scope_lock():
    r = subprocess.run(
        [sys.executable, "scripts/check_bde7_scope_lock.py"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert r.returncode == 0, r.stdout + r.stderr
    assert "BDE(7)" in r.stdout
    assert "poincare_theorem_level_closure" in r.stdout
