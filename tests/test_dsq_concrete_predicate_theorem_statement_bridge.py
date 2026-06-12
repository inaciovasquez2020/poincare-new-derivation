from pathlib import Path
import subprocess


def test_dsq_concrete_predicate_theorem_statement_bridge_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_concrete_predicate_theorem_statement_bridge.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_CONCRETE_PREDICATE_THEOREM_STATEMENT_BRIDGE_FOUND" in result.stdout


def test_dsq_concrete_predicate_theorem_statement_bridge_surface_exists() -> None:
    text = Path("lean/Regge/DSQConcretePredicateTheoremStatementBridge.lean").read_text()
    assert "def DSQConcreteMetricValidityPredicate_theoremStatement" in text
    assert "(p : DSQConcreteMetricValidityPredicate) : Prop" in text
    assert "p.target.theoremStatement" in text
    assert "def DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "theorem DSQ_METRIC_VALIDITY_THEOREM" not in text
    assert "axiom DSQ_METRIC_VALIDITY_THEOREM" not in text
