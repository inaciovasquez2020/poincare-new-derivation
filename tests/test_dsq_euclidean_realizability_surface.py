from pathlib import Path
import subprocess


def test_dsq_euclidean_realizability_surface_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_euclidean_realizability_surface.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_EUCLIDEAN_REALIZABILITY_SURFACE_FOUND" in result.stdout


def test_dsq_euclidean_realizability_surface_exists() -> None:
    text = Path("lean/Regge/DSQEuclideanRealizabilitySurface.lean").read_text()
    assert "def EuclideanRealizable2" in text
    assert "theorem euclideanRealizable2_equilateral" in text
    assert "theorem not_euclideanRealizable2_collinear" in text
    assert "structure DSQEuclideanRealizabilitySurface" in text
    assert "def DSQ_EUCLIDEAN_REALIZABILITY_SURFACE" in text
    assert "cmDet2_pos_of_realizable" not in text
    assert "def DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "theorem DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "axiom DSQ_METRIC_VALIDITY_THEOREM" not in text
