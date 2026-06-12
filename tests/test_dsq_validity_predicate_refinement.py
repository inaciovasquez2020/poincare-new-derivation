from pathlib import Path
import subprocess


def test_dsq_validity_predicate_refinement_verifier_passes() -> None:
    result = subprocess.run(
        ["python3", "tools/verify_dsq_validity_predicate_refinement.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "DSQ_VALIDITY_PREDICATE_REFINEMENT_SURFACE_FOUND" in result.stdout


def test_dsq_validity_predicate_refinement_surface_exists() -> None:
    text = Path("lean/Regge/DSQValidityPredicateRefinement.lean").read_text()
    assert "structure DSQValidityPredicateRefinement where" in text
    assert "binding : DSQEdgeCoordBinding" in text
    assert "isValidInput : binding.inputShape → Prop" in text
    assert "DSQ_VALIDITY_PREDICATE_REFINEMENT" in text
