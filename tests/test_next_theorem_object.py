from pathlib import Path

def test_next_theorem_object_lock():
    text = Path("docs/math/NEXT_THEOREM_OBJECT.md").read_text(encoding="utf-8")
    assert "Next Theorem Object" in text
    assert "Local spherical descent lemma." in text
    assert "Zero-defect characterization." in text
    assert "\\Phi(T)=\\sum_{v\\in T}|d(v)-6|" in text
    assert "Open." in text
