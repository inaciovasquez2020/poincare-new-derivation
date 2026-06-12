from pathlib import Path
import subprocess


def test_dsq_concrete_predicate_input_surface_bridge_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_concrete_predicate_input_surface_bridge.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_CONCRETE_PREDICATE_INPUT_SURFACE_BRIDGE_FOUND" in result.stdout


def test_dsq_concrete_predicate_input_surface_bridge_surface_exists() -> None:
    text = Path("lean/Regge/DSQConcretePredicateInputSurfaceBridge.lean").read_text()
    assert "def DSQConcreteMetricValidityPredicate_to_DSQMetricValidityInputSurface" in text
    assert "(p : DSQConcreteMetricValidityPredicate)" in text
    assert "DSQMetricValidityInputSurface" in text
    assert "DSQ_METRIC_VALIDITY_THEOREM :" not in text
    assert "theorem DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "axiom DSQ_METRIC_VALIDITY_THEOREM" not in text
