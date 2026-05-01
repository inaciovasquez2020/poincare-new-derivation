"""Tests for the PND Conditional Frontier Lock verifier."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
LOCK_PATH = REPO_ROOT / "docs" / "status" / "PND_CONDITIONAL_FRONTIER_LOCK_2026_05_01.md"
VERIFIER_PATH = REPO_ROOT / "scripts" / "verify_pnd_conditional_frontier_lock.py"


def _load_verifier():
    spec = importlib.util.spec_from_file_location(
        "verify_pnd_conditional_frontier_lock",
        VERIFIER_PATH,
    )
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_lock_file_exists() -> None:
    assert LOCK_PATH.is_file()


def test_verifier_returns_no_errors_on_real_lock() -> None:
    verifier = _load_verifier()
    assert verifier.verify(LOCK_PATH) == []


def test_verifier_main_returns_zero_on_real_lock() -> None:
    verifier = _load_verifier()
    assert verifier.main() == 0


def test_verifier_rejects_unqualified_poincare_proved_phrase(tmp_path: Path) -> None:
    verifier = _load_verifier()
    text = LOCK_PATH.read_text(encoding="utf-8")
    bad_lock = tmp_path / "bad_poincare_proved.md"
    bad_lock.write_text(
        text + "\nPoincaré theorem is proved.\n",
        encoding="utf-8",
    )
    errors = verifier.verify(bad_lock)
    assert any("Poincaré theorem is proved" in error for error in errors)


def test_verifier_rejects_unqualified_unconditional_closure_phrase(tmp_path: Path) -> None:
    verifier = _load_verifier()
    text = LOCK_PATH.read_text(encoding="utf-8")
    bad_lock = tmp_path / "bad_unconditional_closure.md"
    bad_lock.write_text(
        text + "\nunconditional closure\n",
        encoding="utf-8",
    )
    errors = verifier.verify(bad_lock)
    assert any("unconditional closure" in error for error in errors)


def test_verifier_allows_status_safe_unconditional_closure_sentence(tmp_path: Path) -> None:
    verifier = _load_verifier()
    text = LOCK_PATH.read_text(encoding="utf-8")
    allowed_lock = tmp_path / "allowed_unconditional_closure.md"
    allowed_lock.write_text(
        text + "\nThis document does not claim unconditional closure.\n",
        encoding="utf-8",
    )
    errors = verifier.verify(allowed_lock)
    assert errors == []
