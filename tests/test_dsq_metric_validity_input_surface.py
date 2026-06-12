from pathlib import Path
import subprocess


def test_dsq_metric_validity_input_surface_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_metric_validity_input_surface.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_METRIC_VALIDITY_INPUT_SURFACE_FOUND" in result.stdout


def test_dsq_metric_validity_input_surface_exists() -> None:
    text = Path("lean/Regge/DSQMetricValidityInputSurface.lean").read_text()
    assert "structure DSQMetricValidityInputSurface where" in text
    assert "refinement : DSQValidityPredicateRefinement" in text
    assert "metricValid :" in text
    assert "DSQ_METRIC_VALIDITY_INPUT_SURFACE" in text
    assert "DSQ_METRIC_VALIDITY_THEOREM" not in text
