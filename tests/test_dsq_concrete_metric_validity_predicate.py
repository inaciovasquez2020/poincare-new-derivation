from pathlib import Path
import subprocess


def test_dsq_concrete_metric_validity_predicate_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_concrete_metric_validity_predicate.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_CONCRETE_METRIC_VALIDITY_PREDICATE_SURFACE_FOUND" in result.stdout


def test_dsq_concrete_metric_validity_predicate_surface_exists() -> None:
    text = Path("lean/Regge/DSQConcreteMetricValidityPredicate.lean").read_text()
    assert "def DSQConcreteMetricCarrierPredicate" in text
    assert "0 < c.vertexCount ∧ 0 < c.edgeCount ∧ 0 < c.simplexCount" in text
    assert "structure DSQConcreteMetricValidityPredicate where" in text
    assert "target : DSQMetricValidityTheoremTarget" in text
    assert "DSQ_CONCRETE_METRIC_VALIDITY_PREDICATE" in text
    assert "def DSQ_METRIC_VALIDITY_THEOREM : Prop" not in text
