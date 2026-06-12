from __future__ import annotations

import json
import subprocess
from pathlib import Path


def test_dsq_input_shape_surface_found() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_input_shape.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_INPUT_SHAPE_SURFACE_FOUND" in result.stdout
    assert "lean/Regge/DSQInputShape.lean:dSq" in result.stdout
    assert "lean/Regge/DSQInputShape.lean:is_valid" in result.stdout


def test_dsq_input_shape_artifact() -> None:
    artifact = Path("artifacts/regge/dsq_input_shape_spec_2026_06_12.json")
    data = json.loads(artifact.read_text())

    assert data["certificate_id"] == "DSQ_INPUT_SHAPE_SPEC_2026_06_12"
    assert data["scope"] == "input_shape_only"
    assert data["lean_module"] == "Regge.DSQInputShape"
    assert data["claim_boundary"]["does_not_define_regge_geometry"] is True
    assert data["claim_boundary"]["does_not_prove_metric_validity"] is True
    assert data["claim_boundary"]["does_not_claim_euclidean_realizability"] is True
    assert data["claim_boundary"]["does_not_close_dsq_theorem"] is True
