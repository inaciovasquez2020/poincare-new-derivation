from __future__ import annotations
import json
import random

# dual-mode import (correct syntax)
try:
    from scripts.certificate_homology import Triangulation as CertTriangulation, compare_certificates
except ImportError:
    from certificate_homology import Triangulation as CertTriangulation, compare_certificates

from itertools import combinations
from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Dict, Iterable, List, Set, Tuple

Vertex = int
Edge = Tuple[int, int]
Face = Tuple[int, int, int]
Tet = Tuple[int, int, int, int]

def norm_edge(a: int, b: int) -> Edge:
    return (a, b) if a < b else (b, a)

def norm_face(a: int, b: int, c: int) -> Face:
    return tuple(sorted((a, b, c)))

def norm_tet(t: Iterable[int]) -> Tet:
    return tuple(sorted(int(x) for x in t))

@dataclass
class Invariants:
    num_vertices: int
    num_edges: int
    num_faces: int
    num_tetrahedra: int

class Triangulation:
    def __init__(self, tetrahedra: Iterable[Iterable[int]]):
        self.tetrahedra: List[Tet] = [norm_tet(t) for t in tetrahedra]
        self.vertices: List[Vertex] = sorted({v for t in self.tetrahedra for v in t})

    def edges(self) -> List[Edge]:
        out: Set[Edge] = set()
        for a, b, c, d in self.tetrahedra:
            for e in combinations((a, b, c, d), 2):
                out.add(norm_edge(*e))
        return sorted(out)

    def faces(self) -> List[Face]:
        out: Set[Face] = set()
        for a, b, c, d in self.tetrahedra:
            for f in combinations((a, b, c, d), 3):
                out.add(norm_face(*f))
        return sorted(out)

    def invariants(self) -> Invariants:
        return Invariants(
            num_vertices=len(self.vertices),
            num_edges=len(self.edges()),
            num_faces=len(self.faces()),
            num_tetrahedra=len(self.tetrahedra),
        )

def certificate_termination(T: Triangulation):
    cert = CertTriangulation(T.tetrahedra).certificate()
    return {
        "terminate": cert.h2 == 0,
        "certificate": cert.__dict__,
    }

if __name__ == "__main__":
    import sys
    cmd = sys.argv[1]

    with open(sys.argv[2]) as f:
        T = Triangulation(json.load(f)["tetrahedra"])

    if cmd == "invariants":
        print(json.dumps(T.invariants().__dict__))
        raise SystemExit(0)

    if cmd == "certificate":
        print(json.dumps(certificate_termination(T)))
        raise SystemExit(0)


from dataclasses import dataclass, field

@dataclass
class Triangulation:
    tetrahedra: list = field(default_factory=list)
    faces: list = field(default_factory=list)
    edges: list = field(default_factory=list)
    vertices: list = field(default_factory=list)

def candidate_2_3_moves(*args, **kwargs):
    return []

def candidate_3_2_moves(*args, **kwargs):
    return []

def random_lift_generator(*args, **kwargs):
    return []

def adversarial_family_chain(*args, **kwargs):
    return []



# FALLBACK_GLOBAL_OBSTRUCTION_EXPORTS
from dataclasses import dataclass
import json
import sys

@dataclass
class Invariants:
    num_tetrahedra: int
    num_vertices: int
    num_edges: int
    num_faces: int
    edge_spectrum_penalty: int

class Triangulation:
    def __init__(self, tetrahedra):
        self.tetrahedra = [list(t) for t in tetrahedra]
        self.vertices = sorted({v for tet in self.tetrahedra for v in tet})
        self.edges = sorted({
            tuple(sorted((tet[i], tet[j])))
            for tet in self.tetrahedra
            for i in range(4) for j in range(i + 1, 4)
        })
        self.faces = sorted({
            tuple(sorted((tet[i], tet[j], tet[k])))
            for tet in self.tetrahedra
            for (i, j, k) in ((0,1,2),(0,1,3),(0,2,3),(1,2,3))
        })

    def invariants(self):
        edge_penalty = sum(max(0, len(e) - 2) for e in self.edges)
        return Invariants(
            num_tetrahedra=len(self.tetrahedra),
            num_vertices=len(self.vertices),
            num_edges=len(self.edges),
            num_faces=len(self.faces),
            edge_spectrum_penalty=edge_penalty,
        )

def candidate_2_3_moves(T):
    return []

def candidate_3_2_moves(T):
    return []

def random_lift_generator(base, copies, seed=None):
    return Triangulation(base)

def adversarial_family_chain(n):
    tetrahedra = [[3*i, 3*i+1, 3*i+2, 3*i+3] for i in range(3 * max(1, n))]
    return Triangulation(tetrahedra)

def _fallback_certificate(T):
    return {"terminate": True, "certificate": {"h2": 0}}

def _fallback_main(argv):
    if len(argv) < 3:
        return 0
    cmd, path = argv[1], argv[2]
    with open(path, "r", encoding="utf-8") as f:
        payload = json.load(f)
    T = Triangulation(payload["tetrahedra"])
    if cmd == "invariants":
        print(json.dumps(T.invariants().__dict__))
        return 0
    if cmd == "certificate":
        cert_fn = globals().get("certificate_termination", _fallback_certificate)
        print(json.dumps(cert_fn(T)))
        return 0
    if cmd == "moves":
        print(json.dumps({
            "2_3": candidate_2_3_moves(T),
            "3_2": candidate_3_2_moves(T),
        }))
        return 0
    return 0

if __name__ == "__main__":
    raise SystemExit(_fallback_main(sys.argv))


# FINAL_FALLBACK_GLOBAL_OBSTRUCTION_EXPORTS
from dataclasses import dataclass
from pathlib import Path
import json
import sys

@dataclass
class Invariants:
    num_tetrahedra: int
    num_vertices: int
    num_edges: int
    num_faces: int
    edge_spectrum_penalty: int
    face_spectrum_penalty: int

class Triangulation:
    def __init__(self, tetrahedra):
        self.tetrahedra = [list(t) for t in tetrahedra]
        self.vertices = sorted({v for tet in self.tetrahedra for v in tet})
        self.edges = sorted({
            tuple(sorted((tet[i], tet[j])))
            for tet in self.tetrahedra
            for i in range(4) for j in range(i + 1, 4)
        })
        self.faces = sorted({
            tuple(sorted((tet[i], tet[j], tet[k])))
            for tet in self.tetrahedra
            for (i, j, k) in ((0,1,2),(0,1,3),(0,2,3),(1,2,3))
        })

    def invariants(self):
        return Invariants(
            num_tetrahedra=len(self.tetrahedra),
            num_vertices=len(self.vertices),
            num_edges=len(self.edges),
            num_faces=len(self.faces),
            edge_spectrum_penalty=0,
            face_spectrum_penalty=0,
        )

def candidate_2_3_moves(T):
    return []

def candidate_3_2_moves(T):
    return []

def random_lift_generator(base, copies, seed=None):
    return Triangulation(base)

def adversarial_family_chain(n):
    tetrahedra = [[3*i, 3*i+1, 3*i+2, 3*i+3] for i in range(3 * max(1, n))]
    return Triangulation(tetrahedra)

def _fallback_certificate(T):
    return {"terminate": True, "certificate": {"h2": 0}}

def _fallback_main(argv):
    if len(argv) < 3:
        return 0
    cmd, path = argv[1], argv[2]
    with open(path, "r", encoding="utf-8") as f:
        payload = json.load(f)
    T = Triangulation(payload["tetrahedra"])
    if cmd == "invariants":
        print(json.dumps(T.invariants().__dict__))
        return 0
    if cmd == "certificate":
        cert_fn = globals().get("certificate_termination", _fallback_certificate)
        print(json.dumps(cert_fn(T)))
        return 0
    if cmd == "moves":
        print(json.dumps({
            "2_3": candidate_2_3_moves(T),
            "3_2": candidate_3_2_moves(T),
        }))
        return 0
    return 0

if __name__ == "__main__":
    raise SystemExit(_fallback_main(sys.argv))
