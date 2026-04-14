from pathlib import Path

def test_stabilize_top3():
    region = Path("docs/foundations/REGION_DEFINITION.md").read_text(encoding="utf-8")
    start = Path("docs/START_HERE.md").read_text(encoding="utf-8")
    outsider = Path("docs/status/OUTSIDER_TASK.md").read_text(encoding="utf-8")

    assert "program-scale theorem artifact" in region
    assert "Local spherical descent lemma." in region
    assert "Zero-defect characterization: Phi(T)=0 => T ≃ S^3." in region

    assert "docs/foundations/REGION_DEFINITION.md" in start
    assert "docs/status/CANONICAL_MISSING_OBJECT.md" in start
    assert "docs/math/NEXT_THEOREM_OBJECT.md" in start

    assert "Local spherical descent lemma." in outsider
    assert "Zero-defect characterization: Phi(T)=0 => T ≃ S^3." in outsider
    assert "conditional" in outsider
