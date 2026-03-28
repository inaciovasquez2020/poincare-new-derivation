from __future__ import annotations
from certificate_homology import Triangulation as CertTriangulation, compare_certificates
import random
import json
from itertools import combinations
from collections import defaultdict, Counter, deque
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

def rank_f2(rows: List[int], ncols: int) -> int:
    rows = [r for r in rows if r != 0]
    rank = 0
    bit = ncols - 1
    while bit >= 0 and rows:
        pivot_idx = None
        mask = 1 << bit
        for i, r in enumerate(rows):
            if r & mask:
                pivot_idx = i
                break
        if pivot_idx is None:
            bit -= 1
            continue
        pivot = rows[pivot_idx]
        rows[pivot_idx], rows[0] = rows[0], rows[pivot_idx]
        new_rows = [rows[0]]
        for r in rows[1:]:
            new_rows.append(r ^ pivot if (r & mask) else r)
        rows = [r for r in new_rows[1:] if r != 0]
        rank += 1
        bit -= 1
    return rank

@dataclass
class Invariants:
    num_vertices: int
    num_edges: int
    num_faces: int
    num_tetrahedra: int
    beta1_graph: int
    beta1_2skeleton_proxy: int
    edge_spectrum_penalty: int
    face_spectrum_penalty: int
    noncollapsible_core_faces: int
    noncollapsible_core_tets: int
    two_skeleton_components: int
    pi1_proxy_rank: int
    certificate: Dict[str, int]

class Triangulation:
    def __init__(self, tetrahedra: Iterable[Iterable[int]]):
        self.tetrahedra: List[Tet] = [norm_tet(t) for t in tetrahedra]
        self.vertices: List[Vertex] = sorted({v for t in self.tetrahedra for v in t})

    def edges(self) -> List[Edge]:
        out: Set[Edge] = set()
        for a, b, c, d in self.tetrahedra:
            out |= {
                norm_edge(a, b), norm_edge(a, c), norm_edge(a, d),
                norm_edge(b, c), norm_edge(b, d), norm_edge(c, d),
            }
        return sorted(out)

    def faces(self) -> List[Face]:
        out: Set[Face] = set()
        for a, b, c, d in self.tetrahedra:
            out |= {
                norm_face(a, b, c), norm_face(a, b, d),
                norm_face(a, c, d), norm_face(b, c, d),
            }
        return sorted(out)

    def edge_to_tets(self) -> Dict[Edge, List[int]]:
        out: Dict[Edge, List[int]] = defaultdict(list)
        for i, t in enumerate(self.tetrahedra):
            for e in combinations(t, 2):
                out[norm_edge(*e)].append(i)
        return out

    def face_to_tets(self) -> Dict[Face, List[int]]:
        out: Dict[Face, List[int]] = defaultdict(list)
        for i, (a, b, c, d) in enumerate(self.tetrahedra):
            for f in [(a, b, c), (a, b, d), (a, c, d), (b, c, d)]:
                out[norm_face(*f)].append(i)
        return out

    def edge_degrees(self) -> Dict[Edge, int]:
        return {e: len(ts) for e, ts in self.edge_to_tets().items()}

    def face_degrees(self) -> Dict[Face, int]:
        return {f: len(ts) for f, ts in self.face_to_tets().items()}

    def one_skeleton_components(self) -> int:
        verts = self.vertices
        if not verts:
            return 0
        adj: Dict[int, Set[int]] = {v: set() for v in verts}
        for u, v in self.edges():
            adj[u].add(v)
            adj[v].add(u)
        seen: Set[int] = set()
        comps = 0
        for v in verts:
            if v in seen:
                continue
            comps += 1
            q = deque([v])
            seen.add(v)
            while q:
                x = q.popleft()
                for y in adj[x]:
                    if y not in seen:
                        seen.add(y)
                        q.append(y)
        return comps

    def beta1_graph(self) -> int:
        V = len(self.vertices)
        E = len(self.edges())
        C = self.one_skeleton_components()
        return E - V + C

    def two_skeleton_components(self) -> int:
        faces = self.faces()
        if not faces:
            return 0
        edge_to_faces: Dict[Edge, List[int]] = defaultdict(list)
        for i, (a, b, c) in enumerate(faces):
            for e in (norm_edge(a, b), norm_edge(a, c), norm_edge(b, c)):
                edge_to_faces[e].append(i)
        adj: Dict[int, Set[int]] = {i: set() for i in range(len(faces))}
        for idxs in edge_to_faces.values():
            for i in idxs:
                for j in idxs:
                    if i != j:
                        adj[i].add(j)
        seen: Set[int] = set()
        comps = 0
        for i in range(len(faces)):
            if i in seen:
                continue
            comps += 1
            q = deque([i])
            seen.add(i)
            while q:
                x = q.popleft()
                for y in adj[x]:
                    if y not in seen:
                        seen.add(y)
                        q.append(y)
        return comps

    def beta1_2skeleton_proxy(self) -> int:
        verts = self.vertices
        edges = self.edges()
        faces = self.faces()
        edge_index = {e: i for i, e in enumerate(edges)}
        rows = []
        for a, b, c in faces:
            row = 0
            for e in (norm_edge(a, b), norm_edge(a, c), norm_edge(b, c)):
                row ^= (1 << edge_index[e])
            rows.append(row)
        rank_d2 = rank_f2(rows, len(edges))
        return len(edges) - len(verts) + self.one_skeleton_components() - rank_d2

    def noncollapsible_core(self) -> Tuple[Set[Face], Set[int]]:
        face_to_tets = self.face_to_tets()
        active_faces: Set[Face] = set(face_to_tets.keys())
        active_tets: Set[int] = set(range(len(self.tetrahedra)))
        changed = True
        while changed:
            changed = False
            free_faces = [f for f in list(active_faces) if len([t for t in face_to_tets[f] if t in active_tets]) <= 1]
            if not free_faces:
                break
            for f in free_faces:
                incident = [t for t in face_to_tets[f] if t in active_tets]
                active_faces.discard(f)
                if incident:
                    t = incident[0]
                    if t in active_tets:
                        active_tets.remove(t)
                        a, b, c, d = self.tetrahedra[t]
                        for g in (norm_face(a, b, c), norm_face(a, b, d), norm_face(a, c, d), norm_face(b, c, d)):
                            if g in active_faces:
                                changed = True
        remaining_faces: Set[Face] = set()
        for f in active_faces:
            if any(t in active_tets for t in face_to_tets[f]):
                remaining_faces.add(f)
        return remaining_faces, active_tets

    def pi1_proxy_rank(self) -> int:
        return max(0, self.beta1_2skeleton_proxy())

    def edge_spectrum_penalty(self) -> int:
        return sum(abs(k - 3) for k in self.edge_degrees().values())

    def face_spectrum_penalty(self) -> int:
        return sum(abs(k - 2) for k in self.face_degrees().values())

    def invariants(self) -> Invariants:
        core_faces, core_tets = self.noncollapsible_core()
        inv = Invariants(
            num_vertices=len(self.vertices),
            num_edges=len(self.edges()),
            num_faces=len(self.faces()),
            num_tetrahedra=len(self.tetrahedra),
            beta1_graph=self.beta1_graph(),
            beta1_2skeleton_proxy=self.beta1_2skeleton_proxy(),
            edge_spectrum_penalty=self.edge_spectrum_penalty(),
            face_spectrum_penalty=self.face_spectrum_penalty(),
            noncollapsible_core_faces=len(core_faces),
            noncollapsible_core_tets=len(core_tets),
            two_skeleton_components=self.two_skeleton_components(),
            pi1_proxy_rank=self.pi1_proxy_rank(),
            certificate={},
        )
        inv.certificate = {
            "beta1_graph": inv.beta1_graph,
            "beta1_2skeleton_proxy": inv.beta1_2skeleton_proxy,
            "noncollapsible_core_tets": inv.noncollapsible_core_tets,
            "two_skeleton_components": inv.two_skeleton_components,
            "pi1_proxy_rank": inv.pi1_proxy_rank,
            "edge_spectrum_penalty": inv.edge_spectrum_penalty,
            "face_spectrum_penalty": inv.face_spectrum_penalty,
        }
        return inv

def bistellar_1_4(T: Triangulation, tet_index: int, new_vertex: int) -> Triangulation:
    keep = [t for i, t in enumerate(T.tetrahedra) if i != tet_index]
    a, b, c, d = T.tetrahedra[tet_index]
    keep.extend([
        norm_tet((new_vertex, a, b, c)),
        norm_tet((new_vertex, a, b, d)),
        norm_tet((new_vertex, a, c, d)),
        norm_tet((new_vertex, b, c, d)),
    ])
    return Triangulation(keep)

def candidate_2_3_moves(T: Triangulation):
    face_to_tets = T.face_to_tets()
    out = []
    for f, inc in face_to_tets.items():
        if len(inc) != 2:
            continue
        t1, t2 = inc
        a, b, c = f
        u = next(iter(set(T.tetrahedra[t1]) - set(f)))
        v = next(iter(set(T.tetrahedra[t2]) - set(f)))
        if u == v:
            continue
        out.append({
            "face": list(f),
            "tetrahedra": [t1, t2],
            "new_edge": list(norm_edge(u, v)),
            "new_tetrahedra": [
                list(norm_tet((u, v, a, b))),
                list(norm_tet((u, v, a, c))),
                list(norm_tet((u, v, b, c))),
            ],
        })
    return out

def candidate_3_2_moves(T: Triangulation):
    edge_to_tets = T.edge_to_tets()
    out = []
    for e, inc in edge_to_tets.items():
        if len(inc) != 3:
            continue
        u, v = e
        opp = []
        for i in inc:
            opp.append(tuple(sorted(set(T.tetrahedra[i]) - {u, v})))
        union = sorted({x for s in opp for x in s})
        if len(union) != 3:
            continue
        out.append({
            "edge": list(e),
            "tetrahedra": inc,
            "opposite_vertices": union,
        })
    return out

def certificate_termination(T: Triangulation) -> Dict[str, object]:
    inv = T.invariants()
    cert = CertTriangulation(T.tetrahedra).certificate()
    return {
        "terminate": (
            inv.beta1_2skeleton_proxy == 0 and
            inv.noncollapsible_core_tets == 0 and
            inv.pi1_proxy_rank == 0 and
            cert.h2 == 0
        ),
        "certificate": {
            **inv.certificate,
            "rank_d2": cert.rank_d2,
            "rank_d3": cert.rank_d3,
            "h2": cert.h2,
            "pi1_generators": cert.pi1_generators,
            "pi1_relators_faces": cert.pi1_relators_faces,
            "pi1_relators_tets": cert.pi1_relators_tets,
            "certificate_metric": list(cert.certificate_metric),
        },
    }

def random_lift_generator(base_tets, lift_size: int, seed: int) -> Triangulation:
    rng = random.Random(seed)
    base_tets = [norm_tet(t) for t in base_tets]
    lifted = []
    for tet in base_tets:
        choices = [rng.randrange(lift_size) for _ in range(4)]
        lifted.append(tuple(v * lift_size + choices[i] for i, v in enumerate(tet)))
    return Triangulation(lifted)

def adversarial_family_chain(n: int) -> Triangulation:
    out = []
    top = 1000
    for i in range(n):
        out.append(norm_tet((0, 1, 2, top + 3 * i)))
        out.append(norm_tet((0, 1, 3, top + 3 * i + 1)))
        out.append(norm_tet((0, 2, 3, top + 3 * i + 2)))
    return Triangulation(out)

if __name__ == "__main__":
    import sys

    cmd = sys.argv[1]

    if cmd == "invariants":
        with open(sys.argv[2]) as f:
            T = Triangulation(json.load(f)["tetrahedra"])
        print(json.dumps(T.invariants().__dict__))
        raise SystemExit(0)

    if cmd == "certificate":
        with open(sys.argv[2]) as f:
            T = Triangulation(json.load(f)["tetrahedra"])
        print(json.dumps(certificate_termination(T)))
        raise SystemExit(0)

    if cmd == "moves":
        with open(sys.argv[2]) as f:
            T = Triangulation(json.load(f)["tetrahedra"])
        print(json.dumps({
            "2_3": candidate_2_3_moves(T),
            "3_2": candidate_3_2_moves(T),
        }))
        raise SystemExit(0)

    if cmd == "random_lift":
        with open(sys.argv[2]) as f:
            base = json.load(f)["tetrahedra"]
        T = random_lift_generator(base, int(sys.argv[3]), int(sys.argv[4]))
        print(json.dumps(T.invariants().__dict__))
        raise SystemExit(0)

    if cmd == "adversarial":
        T = adversarial_family_chain(int(sys.argv[2]))
        print(json.dumps(T.invariants().__dict__))
        raise SystemExit(0)
