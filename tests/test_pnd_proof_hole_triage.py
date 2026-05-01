from pathlib import Path

DOC = Path("docs/status/PND_PROOF_HOLE_TRIAGE_2026_05_01.md")

def test_doc_exists():
    assert DOC.exists()

def test_conditional_boundary():
    text = DOC.read_text()
    assert "Conditional." in text
    assert "This is a proof-hole inventory only. It does not assert theorem-level closure." in text
    assert "No unconditional Poincaré theorem is asserted." in text

def test_counts_present():
    text = DOC.read_text()
    assert "Total `sorry`:" in text
    assert "Total `admit`:" in text
    assert "Total `axiom`:" in text
    assert "Total holes:" in text

def test_first_target_present():
    text = DOC.read_text()
    assert "lean/Poincare/FinalConstructive.lean" in text
    assert "Replace exactly one `by sorry`" in text
