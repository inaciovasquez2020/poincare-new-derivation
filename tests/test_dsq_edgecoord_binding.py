from pathlib import Path
import subprocess


def test_dsq_edgecoord_binding_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_edgecoord_binding.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_EDGECOORD_BINDING_SURFACE_FOUND" in result.stdout


def test_dsq_edgecoord_binding_lean_surface_exists() -> None:
    text = Path("lean/Regge/DSQEdgeCoordBinding.lean").read_text()
    assert "structure DSQReggeComplex where" in text
    assert "structure DSQEdgeCoordBinding where" in text
    assert "DSQ_EDGECOORD_BINDING_TO_REGGE_COMPLEX" in text
    assert "realizesDSQInputShape : inputShape = DSQInputShape" in text
