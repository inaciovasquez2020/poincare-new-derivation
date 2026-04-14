from pathlib import Path

def test_frontier_registry_consistency():
    readme = Path("README.md").read_text(encoding="utf-8")
    status = Path("STATUS.md").read_text(encoding="utf-8")
    missing = Path("docs/status/CANONICAL_MISSING_OBJECT.md").read_text(encoding="utf-8")
    open_lemmas = Path("docs/conditional_gap/OPEN_LEMMAS.md").read_text(encoding="utf-8")
    final_wall = Path("docs/math/FINAL_WALL_LOCAL_SPHERICAL_DESCENT.md").read_text(encoding="utf-8")
    zero_defect = Path("docs/math/ZERO_DEFECT_BRIDGE.md").read_text(encoding="utf-8")
    delta_schema = Path("docs/math/LOCAL_DELTA_CERTIFICATE_SCHEMA.md").read_text(encoding="utf-8")

    assert "Local spherical descent lemma" in readme
    assert "Zero-defect characterization" in readme

    assert "normalization bridge: active" in status
    assert "full closure: conditional" in status

    assert "Local spherical descent lemma." in missing
    assert "Zero-defect characterization: Phi(T)=0 => T ≃ S^3." in missing
    assert "Local spherical descent lemma" in open_lemmas
    assert "Zero-defect characterization: Phi(T)=0 ⇒ T ≃ S^3" in open_lemmas

    assert "Final Wall — Local Spherical Descent" in final_wall
    assert "Zero-Defect Bridge" in zero_defect
    assert "Local Delta Certificate Schema" in delta_schema
