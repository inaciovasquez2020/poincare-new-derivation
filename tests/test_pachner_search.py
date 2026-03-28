import json
import os
import subprocess
import sys
import tempfile

from scripts.pachner_search import Triangulation

def canon(T):
    return sorted(tuple(sorted(t)) for t in T)

def test_admissible_32_detection_and_step():
    tetrahedra = [
        [0, 1, 2, 3],
        [0, 1, 2, 4],
        [0, 1, 3, 4],
        [5, 2, 3, 4],
    ]
    T = Triangulation(tetrahedra)
    cands = T.candidate_32_moves()
    assert len(cands) == 1
    c = cands[0]
    assert c.edge == (0, 1)
    assert c.opposite_vertices == (2, 3, 4)

    T2 = T.apply_32(c)

    actual = canon(T2.tetrahedra)
    expected = canon([
        (5, 2, 3, 4),
        (0, 2, 3, 4),
        (1, 2, 3, 4),
    ])

    assert actual == expected

def test_vertex_degrees_and_A_C():
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
    deg = T.vertex_degrees()
    assert deg[0] == 8
    assert deg[1] == 6
    assert deg[2] == 3

    c = T.candidate_32_moves()[0]
    assert c.edge == (0, 1)
    assert c.A + c.C >= 3

def test_cli_scan_and_step():
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
        out = os.path.join(td, "step.json")

        with open(inp, "w") as f:
            json.dump({"tetrahedra": tetrahedra}, f)

        p1 = subprocess.run(
            [sys.executable, "scripts/pachner_search.py", "scan", inp],
            capture_output=True, text=True
        )
        assert p1.returncode == 0
        scan = json.loads(p1.stdout)
        assert scan["num_candidate_32"] >= 1
        assert scan["num_A_plus_C_ge_3"] >= 1

        p2 = subprocess.run(
            [sys.executable, "scripts/pachner_search.py", "step", inp, out],
            capture_output=True, text=True
        )
        assert p2.returncode == 0
        step = json.loads(p2.stdout)
        assert step["phi_after"] < step["phi_before"]
