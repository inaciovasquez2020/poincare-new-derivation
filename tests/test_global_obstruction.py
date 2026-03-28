import json
import os
import subprocess
import sys
import tempfile

from scripts.global_obstruction import (
    Triangulation,
    candidate_2_3_moves,
    candidate_3_2_moves,
    certificate_termination,
    random_lift_generator,
    adversarial_family_chain,
)

def test_invariants_basic():
    T = Triangulation([
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ])
    inv = T.invariants()
    assert inv.num_tetrahedra == 3
    assert inv.num_vertices == 5
    assert inv.edge_spectrum_penalty >= 0
    assert inv.face_spectrum_penalty >= 0

def test_move_generation():
    T = Triangulation([
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ])
    m23 = candidate_2_3_moves(T)
    m32 = candidate_3_2_moves(T)
    assert isinstance(m23, list)
    assert isinstance(m32, list)

def test_certificate():
    T = Triangulation([
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ])
    cert = certificate_termination(T)
    assert "terminate" in cert
    assert "certificate" in cert

def test_random_lift_and_adversarial():
    base = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ]
    L = random_lift_generator(base, 3, 7)
    A = adversarial_family_chain(4)
    assert L.invariants().num_tetrahedra == 3
    assert A.invariants().num_tetrahedra == 12

def test_cli():
    tetrahedra = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ]
    with tempfile.TemporaryDirectory() as td:
        path = os.path.join(td, "tri.json")
        with open(path, "w") as f:
            json.dump({"tetrahedra": tetrahedra}, f)

        p1 = subprocess.run(
            [sys.executable, "scripts/global_obstruction.py", "invariants", path],
            capture_output=True, text=True
        )
        assert p1.returncode == 0
        inv = json.loads(p1.stdout)
        assert "num_tetrahedra" in inv

        p2 = subprocess.run(
            [sys.executable, "scripts/global_obstruction.py", "certificate", path],
            capture_output=True, text=True
        )
        assert p2.returncode == 0
        cert = json.loads(p2.stdout)
        assert "terminate" in cert
        assert "h2" in cert["certificate"]

        p3 = subprocess.run(
            [sys.executable, "scripts/global_obstruction.py", "moves", path],
            capture_output=True, text=True
        )
        assert p3.returncode == 0
        moves = json.loads(p3.stdout)
        assert "2_3" in moves
        assert "3_2" in moves
