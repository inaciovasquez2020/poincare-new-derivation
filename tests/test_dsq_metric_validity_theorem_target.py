from pathlib import Path
import subprocess


def test_dsq_metric_validity_theorem_target_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_metric_validity_theorem_target.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_METRIC_VALIDITY_THEOREM_TARGET_SURFACE_FOUND" in result.stdout


def test_dsq_metric_validity_theorem_target_shell_exists() -> None:
    text = Path("lean/Regge/DSQMetricValidityTheoremTarget.lean").read_text()
    assert "structure DSQMetricValidityTheoremTarget where" in text
    assert "surface : DSQMetricValidityInputSurface" in text
    assert "theoremStatement : Prop" in text
    assert "realizesMetricValidityStatement :" in text
    assert "DSQ_METRIC_VALIDITY_THEOREM_TARGET" in text
    assert "def DSQ_METRIC_VALIDITY_THEOREM : Prop" not in text
