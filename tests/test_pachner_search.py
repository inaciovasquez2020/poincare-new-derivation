import json
import os
import subprocess
import sys
import tempfile

from scripts.pachner_search import Triangulation, random_lift_generator, adversarial_family_chain

def canon(T):
    return sorted(tuple(sorted(t)) for t in T)

def test_admissible_32_detection_and_step():
    tetrahedra = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ]
    T = Triangulation(tetrahedra)
    assert T.is_admissible()
    cands = T.candidate_32_moves()
    assert len(cands) == 1
    c = cands[0]
    assert c.edge == (0, 1)
    assert c.opposite_vertices == (2, 3, 4)

    T2 = T.apply_32(c)

    actual = canon(T2.tetrahedra)
    expected = canon([
        (0, 2, 3, 4),
        (1, 2, 3, 4),
    ])
    assert actual == expected
    assert T2.is_admissible()

def test_invalid_complex_is_rejected_by_move_search():
    tetrahedra = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
        [0, 5, 6, 7],
        [0, 8, 9, 10],
        [0, 11, 12, 13],
        [0, 14, 15, 16],
        [0, 17, 18, 19],
        [1, 20, 21, 22],
        [1, 23, 24, 25],
        [1, 26, 27, 28],
        [29, 2, 3, 4],
    ]
    T = Triangulation(tetrahedra)
    assert not T.is_admissible()
    assert T.candidate_32_moves() == []
    assert T.positive_32_moves() == []
    assert T.zero_32_moves() == []

def test_candidate_rejected_when_result_overfills_face():
    tetrahedra = [
        [0, 1, 2, 3],
        [0, 1, 3, 4],
        [0, 1, 2, 4],
        [5, 2, 3, 4],
    ]
    T = Triangulation(tetrahedra)
    assert T.is_admissible()
    assert T.candidate_32_moves() == []


def test_explicit_single_tetrahedron_fixture_is_admissible():
    ball = Triangulation([[0, 1, 2, 3]])
    assert ball.is_admissible()
    assert ball.vertex_degrees() == {0: 1, 1: 1, 2: 1, 3: 1}


def test_face_incidence_and_degree_four_rejection():
    overfull_face = Triangulation([
        [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 5]
    ])
    assert any("face has 3 incident tetrahedra" in e for e in overfull_face.admissibility_errors())

    degree_four = Triangulation([
        [0, 1, 2, 3], [0, 4, 5, 6], [0, 7, 8, 9], [0, 10, 11, 12]
    ])
    assert any("degree-four vertex rejected: 0" in e for e in degree_four.admissibility_errors())


def test_cli_scan_and_zero_witness():
    tetrahedra = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
        [0, 5, 6, 7],
        [0, 8, 9, 10],
        [0, 11, 12, 13],
        [0, 14, 15, 16],
        [0, 17, 18, 19],
        [1, 20, 21, 22],
        [1, 23, 24, 25],
        [1, 26, 27, 28],
        [29, 2, 3, 4],
    ]

    with tempfile.TemporaryDirectory() as td:
        inp = os.path.join(td, "triangulation.json")
        with open(inp, "w") as f:
            json.dump({"tetrahedra": tetrahedra}, f)

        p1 = subprocess.run(
            [sys.executable, "scripts/pachner_search.py", "scan", inp],
            capture_output=True, text=True
        )
        assert p1.returncode == 0
        scan = json.loads(p1.stdout)
        assert "triples" in scan
        assert all({"A", "C", "delta"} <= set(t.keys()) for t in scan["triples"])

        p2 = subprocess.run(
            [sys.executable, "scripts/pachner_search.py", "find_zero_witness", inp],
            capture_output=True, text=True
        )
        assert p2.returncode == 0
        witness = json.loads(p2.stdout)
        assert "num_witnesses" in witness

def test_phi4_entropy_spectrum_random_lift_and_adversarial():
    base = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ]
    T = random_lift_generator(base, 3, 7)
    assert T.is_admissible()
    assert isinstance(T.phi4(), int)
    assert T.phi4() >= 0
    assert isinstance(T.entropy(), float)
    assert T.spectrum_penalty() >= 0

    A = adversarial_family_chain(4)
    assert A.phi4() >= 0
    assert A.spectrum_penalty() >= 0
