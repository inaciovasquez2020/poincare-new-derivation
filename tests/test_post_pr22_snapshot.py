from pathlib import Path

def test_post_pr22_snapshot_lock():
    text = Path("docs/status/POST_PR22_SNAPSHOT.md").read_text(encoding="utf-8")
    assert "Conditional." in text
    assert "Local spherical descent lemma." in text
    assert "Zero-defect characterization: Phi(T)=0 => T ≃ S^3." in text
    assert "Executable artifact status is stable." in text
