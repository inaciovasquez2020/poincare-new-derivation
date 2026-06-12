from pathlib import Path
import subprocess


def test_dsq_triangle_euclidean_input_surface_bridge_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_triangle_euclidean_input_surface_bridge.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_TRIANGLE_EUCLIDEAN_INPUT_SURFACE_BRIDGE_FOUND" in result.stdout


def test_dsq_triangle_euclidean_input_surface_bridge_exists() -> None:
    text = Path("lean/Regge/DSQTriangleEuclideanInputSurfaceBridge.lean").read_text()
    assert "def DSQTriangleEuclideanMetricValidityInputSurface" in text
    assert "structure DSQTriangleEuclideanInputSurfaceBridge" in text
    assert "source : DSQEuclideanRealizabilitySurface" in text
    assert "target : DSQMetricValidityInputSurface" in text
    assert "def DSQ_TRIANGLE_EUCLIDEAN_INPUT_SURFACE_BRIDGE" in text
    assert "def DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "theorem DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "axiom DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "cmDet2_pos_of_realizable" not in text
