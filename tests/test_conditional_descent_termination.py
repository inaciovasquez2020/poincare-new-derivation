from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from conditional_descent_termination import (
    descent_length_bound,
    is_strict_descent_chain,
    is_strict_descent_step,
    terminal_height,
    verify_descent_chain,
)


def test_strict_descent_step() -> None:
    assert is_strict_descent_step(3, 2)
    assert is_strict_descent_step(1, 0)
    assert not is_strict_descent_step(2, 2)
    assert not is_strict_descent_step(2, 3)


def test_strict_descent_chain() -> None:
    assert is_strict_descent_chain([5, 4, 2, 0])
    assert not is_strict_descent_chain([5, 4, 4, 0])
    assert not is_strict_descent_chain([5, 6])


def test_descent_certificate() -> None:
    cert = verify_descent_chain([7, 5, 3, 2, 0])
    assert cert.theorem_id == "PND-CDT-1"
    assert cert.status == "PASS"
    assert cert.step_count == 4
    assert cert.initial_height == 7
    assert cert.final_height == 0
    assert cert.bound_respected is True


def test_descent_length_bound() -> None:
    assert descent_length_bound(0) == 0
    assert descent_length_bound(12) == 12


def test_terminal_height() -> None:
    assert terminal_height([4, 2, 1, 0]) == 0


def test_repository_scope_verifier_passes() -> None:
    result = subprocess.run(
        [sys.executable, "scripts/verify_conditional_descent_termination.py"],
        cwd=ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    assert '"theorem_id": "PND-CDT-1"' in result.stdout
    assert '"status": "PASS"' in result.stdout


def test_nonclaim_boundary_retained() -> None:
    status = (ROOT / "STATUS.md").read_text(encoding="utf-8")
    theorem = (ROOT / "docs/math/CONDITIONAL_DESCENT_TERMINATION_THEOREM.md").read_text(encoding="utf-8")
    assert "No repository-level claim of a Poincare proof." in status
    assert "No repository-level claim of move-system completeness." in status
    assert "This does not prove the Poincare conjecture." in theorem
    assert "remaining mathematical frontier" in theorem
