from pathlib import Path
import subprocess


def test_dsq_concrete_predicate_realization_bridge_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_concrete_predicate_realization_bridge.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_CONCRETE_PREDICATE_REALIZATION_BRIDGE_FOUND" in result.stdout


def test_dsq_concrete_predicate_realization_bridge_surface_exists() -> None:
    text = Path("lean/Regge/DSQConcretePredicateRealizationBridge.lean").read_text()
    assert "def DSQConcreteMetricValidityPredicate_realizesMetricValidityStatement" in text
    assert "DSQConcreteMetricValidityPredicate_theoremStatement p =" in text
    assert "p.target.realizesMetricValidityStatement" in text
    assert "def DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "theorem DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "axiom DSQ_METRIC_VALIDITY_THEOREM" not in text
