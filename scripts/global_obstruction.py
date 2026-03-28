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
