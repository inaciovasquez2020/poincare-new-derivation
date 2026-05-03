import subprocess
from pathlib import Path

DOC = Path("docs/status/PND_D3EL_COUPLED_DISCHARGE_FRONTIER_2026_05_03.md")


def test_pnd_d3el_coupled_discharge_frontier_doc_exists():
    assert DOC.exists()


def test_pnd_d3el_coupled_discharge_frontier_verifier_passes():
    subprocess.run(
        ["python3", "scripts/verify_pnd_d3el_coupled_discharge_frontier.py"],
        check=True,
    )


def test_pnd_d3el_boundary_tokens():
    text = DOC.read_text()
    assert "OPEN_FRONTIER" in text
    assert "This document does not prove PND-D3EL" in text
    assert "This document does not assert unconditional theorem-level closure" in text
    assert "Build success verifies artifact integrity only" in text


def test_pnd_d3el_five_primitives_locked():
    text = DOC.read_text()
    for token in [
        "`PLManifoldLike`",
        "`ExposedFeatures`",
        "`LocalDegree`",
        "`MoveAdmissible`",
        "`BarrierHeight`",
    ]:
        assert token in text
