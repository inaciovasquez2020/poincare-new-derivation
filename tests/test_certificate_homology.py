import json
import os
import subprocess
import sys
import tempfile

from scripts.certificate_homology import Triangulation, compare_certificates

def test_d2_d3_h2_shapes():
    T = Triangulation([
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ])
    d2, edges, faces = T.d2_matrix_f2_rows()
    d3, faces2, tets = T.d3_matrix_f2_rows()
    assert len(d2) == len(faces)
    assert len(d3) == len(tets)
    assert faces == faces2

def test_h2_and_pi1_presentation():
    T = Triangulation([
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ])
    h = T.h2_f2()
    p = T.pi1_presentation()
    assert "h2" in h
    assert "num_generators" in p
    assert p["num_generators"] >= 0

def test_certificate_metric():
    T1 = Triangulation([
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ])
    T2 = Triangulation([
        [0, 1, 2, 3],
    ])
    c1 = T1.certificate()
    c2 = T2.certificate()
    assert compare_certificates(c1, c2) in (-1, 0, 1)

def test_cli_certificate_tools():
    tetrahedra = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
    ]
    with tempfile.TemporaryDirectory() as td:
        path = os.path.join(td, "tri.json")
        with open(path, "w") as f:
            json.dump({"tetrahedra": tetrahedra}, f)

        for cmd, key in [
            ("d2", "rows"),
            ("d3", "rows"),
            ("h2", "h2"),
            ("pi1", "generators"),
            ("certificate", "certificate_metric"),
        ]:
            p = subprocess.run(
                [sys.executable, "scripts/certificate_homology.py", cmd, path],
                capture_output=True, text=True
            )
            assert p.returncode == 0
            data = json.loads(p.stdout)
            assert key in data
