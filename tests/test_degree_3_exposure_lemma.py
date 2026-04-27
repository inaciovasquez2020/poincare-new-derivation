from pathlib import Path

DOC = Path("docs/math/DEGREE_3_EXPOSURE_LEMMA.md")

def test_degree_3_exposure_doc_exists():
    assert DOC.exists()

def test_single_step_edge_imbalance_marked_false():
    text = DOC.read_text(encoding="utf-8")
    assert "is false as stated" in text
    assert "boundary of the regular \\(600\\)-cell" in text
    assert "\\deg(e)=5" in text
    assert "\\neg\\exists e\\;(\\deg(e)=3)" in text

def test_replacement_target_is_degree_3_exposure():
    text = DOC.read_text(encoding="utf-8")
    assert "Replacement theorem object" in text
    assert "T_0=T" in text
    assert "T_{i+1}\\in\\mathcal M(T_i)" in text
    assert "\\Phi(T_i)\\le \\Phi(T)" in text
    assert "\\deg(e)=3" in text
    assert "A(e)+C(e)\\ge 3" in text

def test_status_remains_open_and_no_overclaim():
    text = DOC.read_text(encoding="utf-8")
    assert "This lemma is **Open**." in text
    assert "No theorem-level Poincaré claim follows" in text
    assert "without load-bearing axioms or `sorry` holes" in text
