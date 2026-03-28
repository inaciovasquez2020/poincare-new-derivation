from __future__ import annotations
import json
from itertools import combinations
from collections import defaultdict
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

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

def rank_f2(rows: List[int], ncols: int) -> int:
    rows = [r for r in rows if r != 0]
    rank = 0
    bit = ncols - 1
    while bit >= 0 and rows:
        pivot = None
        mask = 1 << bit
        for i, r in enumerate(rows):
            if r & mask:
                pivot = i
                break
        if pivot is None:
            bit -= 1
            continue
        rows[0], rows[pivot] = rows[pivot], rows[0]
        p = rows[0]
        new_rows = [p]
        for r in rows[1:]:
            new_rows.append(r ^ p if (r & mask) else r)
        rows = [r for r in new_rows[1:] if r != 0]
        rank += 1
        bit -= 1
    return rank

@dataclass
class Certificate:
    rank_d2: int
    rank_d3: int
    dim_c1: int
    dim_c2: int
    dim_c3: int
    beta1_2skeleton: int
    h2: int
    pi1_generators: int
    pi1_relators_faces: int
    pi1_relators_tets: int
    certificate_metric: Tuple[int, int, int, int, int]

class Triangulation:
    def __init__(self, tetrahedra: Iterable[Iterable[int]]):
        self.tetrahedra: List[Tet] = [norm_tet(t) for t in tetrahedra]
        self.vertices: List[Vertex] = sorted({v for t in self.tetrahedra for v in t})

    def edges(self) -> List[Edge]:
        out = set()
        for a, b, c, d in self.tetrahedra:
            out |= {
                norm_edge(a, b), norm_edge(a, c), norm_edge(a, d),
                norm_edge(b, c), norm_edge(b, d), norm_edge(c, d),
            }
        return sorted(out)

    def faces(self) -> List[Face]:
        out = set()
        for a, b, c, d in self.tetrahedra:
            out |= {
                norm_face(a, b, c), norm_face(a, b, d),
                norm_face(a, c, d), norm_face(b, c, d),
            }
        return sorted(out)

    def d2_matrix_f2_rows(self) -> Tuple[List[int], List[Edge], List[Face]]:
        edges = self.edges()
        faces = self.faces()
        edge_index = {e: i for i, e in enumerate(edges)}
        rows: List[int] = []
        for f in faces:
            a, b, c = f
            row = 0
            for e in (norm_edge(a, b), norm_edge(a, c), norm_edge(b, c)):
                row ^= (1 << edge_index[e])
            rows.append(row)
        return rows, edges, faces

    def d3_matrix_f2_rows(self) -> Tuple[List[int], List[Face], List[Tet]]:
        faces = self.faces()
        tets = self.tetrahedra
        face_index = {f: i for i, f in enumerate(faces)}
        rows: List[int] = []
        for t in tets:
            a, b, c, d = t
            row = 0
            for f in (
                norm_face(a, b, c),
                norm_face(a, b, d),
                norm_face(a, c, d),
                norm_face(b, c, d),
            ):
                row ^= (1 << face_index[f])
            rows.append(row)
        return rows, faces, tets

    def h2_f2(self) -> Dict[str, int]:
        d2_rows, edges, faces = self.d2_matrix_f2_rows()
        d3_rows, faces2, tets = self.d3_matrix_f2_rows()
        assert faces == faces2
        rank_d2 = rank_f2(d2_rows, len(edges))
        rank_d3 = rank_f2(d3_rows, len(faces))
        ker_d2 = len(faces) - rank_d2
        h2 = ker_d2 - rank_d3
        beta1_2 = len(edges) - len(self.vertices) + self.num_components_1skeleton() - rank_d2
        return {
            "rank_d2": rank_d2,
            "rank_d3": rank_d3,
            "dim_c1": len(edges),
            "dim_c2": len(faces),
            "dim_c3": len(tets),
            "beta1_2skeleton": beta1_2,
            "h2": h2,
        }

    def num_components_1skeleton(self) -> int:
        verts = self.vertices
        if not verts:
            return 0
        adj: Dict[int, set[int]] = {v: set() for v in verts}
        for u, v in self.edges():
            adj[u].add(v)
            adj[v].add(u)
        seen = set()
        comps = 0
        for v in verts:
            if v in seen:
                continue
            comps += 1
            stack = [v]
            seen.add(v)
            while stack:
                x = stack.pop()
                for y in adj[x]:
                    if y not in seen:
                        seen.add(y)
                        stack.append(y)
        return comps

    def pi1_presentation(self) -> Dict[str, object]:
        edges = self.edges()
        faces = self.faces()
        edge_names = {e: f"e_{i}" for i, e in enumerate(edges)}

        face_relators: List[List[str]] = []
        for a, b, c in faces:
            face_relators.append([
                edge_names[norm_edge(a, b)],
                edge_names[norm_edge(b, c)],
                edge_names[norm_edge(a, c)],
            ])

        tet_relators: List[List[int]] = []
        for t in self.tetrahedra:
            a, b, c, d = t
            tet_relators.append([
                faces.index(norm_face(a, b, c)),
                faces.index(norm_face(a, b, d)),
                faces.index(norm_face(a, c, d)),
                faces.index(norm_face(b, c, d)),
            ])

        return {
            "generators": [edge_names[e] for e in edges],
            "face_relators": face_relators,
            "tet_face_relators": tet_relators,
            "num_generators": len(edges),
            "num_face_relators": len(face_relators),
            "num_tet_relators": len(tet_relators),
        }

    def certificate(self) -> Certificate:
        h = self.h2_f2()
        p = self.pi1_presentation()
        return Certificate(
            rank_d2=h["rank_d2"],
            rank_d3=h["rank_d3"],
            dim_c1=h["dim_c1"],
            dim_c2=h["dim_c2"],
            dim_c3=h["dim_c3"],
            beta1_2skeleton=h["beta1_2skeleton"],
            h2=h["h2"],
            pi1_generators=p["num_generators"],
            pi1_relators_faces=p["num_face_relators"],
            pi1_relators_tets=p["num_tet_relators"],
            certificate_metric=(
                int(h["beta1_2skeleton"] != 0),
                int(h["h2"] != 0),
                p["num_generators"],
                -h["rank_d2"],
                -h["rank_d3"],
            ),
        )

def compare_certificates(a: Certificate, b: Certificate) -> int:
    if a.certificate_metric < b.certificate_metric:
        return -1
    if a.certificate_metric > b.certificate_metric:
        return 1
    return 0

if __name__ == "__main__":
    import sys

    cmd = sys.argv[1]
    with open(sys.argv[2]) as f:
        T = Triangulation(json.load(f)["tetrahedra"])

    if cmd == "d2":
        rows, edges, faces = T.d2_matrix_f2_rows()
        print(json.dumps({
            "ncols": len(edges),
            "nrows": len(faces),
            "edges": [list(e) for e in edges],
            "faces": [list(f) for f in faces],
            "rows": rows,
        }))
        raise SystemExit(0)

    if cmd == "d3":
        rows, faces, tets = T.d3_matrix_f2_rows()
        print(json.dumps({
            "ncols": len(faces),
            "nrows": len(tets),
            "faces": [list(f) for f in faces],
            "tets": [list(t) for t in tets],
            "rows": rows,
        }))
        raise SystemExit(0)

    if cmd == "h2":
        print(json.dumps(T.h2_f2()))
        raise SystemExit(0)

    if cmd == "pi1":
        print(json.dumps(T.pi1_presentation()))
        raise SystemExit(0)

    if cmd == "certificate":
        print(json.dumps(T.certificate().__dict__))
        raise SystemExit(0)
