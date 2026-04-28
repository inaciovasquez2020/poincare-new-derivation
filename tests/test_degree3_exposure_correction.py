import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def test_degree3_exposure_correction_status():
    r = subprocess.run(
        [sys.executable, "scripts/check_degree3_exposure_correction.py"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert r.returncode == 0, r.stdout + r.stderr
    assert "bounded_BDE_N_or_global_barrier_descent" in r.stdout
    assert "poincare_theorem_level_closure" in r.stdout
