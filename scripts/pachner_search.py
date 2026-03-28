from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import combinations
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

Vertex = int
Tet = Tuple[Vertex, Vertex, Vertex, Vertex]
Edge = Tuple[Vertex, Vertex]
Face = Tuple[Vertex, Vertex, Vertex]


def norm_tet(t: Sequence[int]) -> Tet:
    s = tuple(sorted(int(x) for x in t))
    if len(s) != 4 or len(set(s)) != 4:
        raise ValueError(f"Invalid tetrahedron: {t}")
    return s  # type: ignore[return-value]


def norm_edge(a: int, b: int) -> Edge:
    if a == b:
        raise ValueError("Degenerate edge.")
    return (a, b) if a < b else (b, a)


def norm_face(a: int, b: int, c: int) -> Face:
    if len({a, b, c}) != 3:
        raise ValueError("Degenerate face.")
    return tuple(sorted((a, b, c)))  # type: ignore[return-value]


@dataclass(frozen=True)
class Move32Candidate:
    edge: Edge
    tetrahedra: Tuple[Tet, Tet, Tet]
    opposite_vertices: Tuple[Vertex, Vertex, Vertex]
    A: int
    C: int
    delta_phi: int


class Triangulation:
    def __init__(self, tetrahedra: Iterable[Sequence[int]]):
        self.tetrahedra: List[Tet] = [norm_tet(t) for t in tetrahedra]
        if len(self.tetrahedra) != len(set(self.tetrahedra)):
            raise ValueError("Duplicate tetrahedra detected.")
        self.vertices = sorted({v for t in self.tetrahedra for v in t})

    def vertex_degrees(self) -> Dict[Vertex, int]:
        deg: Dict[Vertex, int] = {v: 0 for v in self.vertices}
        for t in self.tetrahedra:
            for v in t:
                deg[v] += 1
        return deg

    def phi(self) -> int:
        deg = self.vertex_degrees()
        return sum(abs(d - 6) for d in deg.values())

    def edge_to_tets(self) -> Dict[Edge, List[Tet]]:
        e2t: Dict[Edge, List[Tet]] = defaultdict(list)
        for t in self.tetrahedra:
            for a, b in combinations(t, 2):
                e2t[norm_edge(a, b)].append(t)
        return e2t

    def face_to_tets(self) -> Dict[Face, List[Tet]]:
        f2t: Dict[Face, List[Tet]] = defaultdict(list)
        for t in self.tetrahedra:
            a, b, c, d = t
            for f in (
                norm_face(a, b, c),
                norm_face(a, b, d),
                norm_face(a, c, d),
                norm_face(b, c, d),
            ):
                f2t[f].append(t)
        return f2t

    def closed_pseudomanifold_faces(self) -> bool:
        f2t = self.face_to_tets()
        return all(len(v) == 2 for v in f2t.values())

    def candidate_32_moves(self) -> List[Move32Candidate]:
        deg = self.vertex_degrees()
        out: List[Move32Candidate] = []
        for edge, incident in self.edge_to_tets().items():
            if len(incident) != 3:
                continue
            u, v = edge
            opp = []
            local_faces = Counter()
            for t in incident:
                rem = [x for x in t if x not in edge]
                if len(rem) != 2:
                    break
                a, b = rem
                opp_vertex = next(iter(set(t) - {u, v, a, b}))
                del opp_vertex
                face = norm_face(a, b, u)
                local_faces[face] += 0
                opp.append(tuple(rem))
            else:
                pass

            opp_set = sorted(set(x for pair in opp for x in pair))
            if len(opp_set) != 3:
                continue

            w1, w2, w3 = opp_set
            required = {
                norm_tet((u, v, w1, w2)),
                norm_tet((u, v, w1, w3)),
                norm_tet((u, v, w2, w3)),
            }
            if set(incident) != required:
                continue

            new_face = norm_face(w1, w2, w3)
            face_inc = self.face_to_tets().get(new_face, [])
            if face_inc:
                continue

            A = int(deg[u] > 6) + int(deg[v] > 6)
            C = int(deg[w1] < 6) + int(deg[w2] < 6) + int(deg[w3] < 6)

            before = (
                abs(deg[u] - 6)
                + abs(deg[v] - 6)
                + abs(deg[w1] - 6)
                + abs(deg[w2] - 6)
                + abs(deg[w3] - 6)
            )
            after = (
                abs((deg[u] - 3) - 6)
                + abs((deg[v] - 3) - 6)
                + abs((deg[w1] - 1) - 6)
                + abs((deg[w2] - 1) - 6)
                + abs((deg[w3] - 1) - 6)
            )
            delta_phi = before - after

            out.append(
                Move32Candidate(
                    edge=edge,
                    tetrahedra=tuple(sorted(required)),
                    opposite_vertices=(w1, w2, w3),
                    A=A,
                    C=C,
                    delta_phi=delta_phi,
                )
            )
        return out

    def apply_32(self, cand: Move32Candidate) -> "Triangulation":
        u, v = cand.edge
        w1, w2, w3 = cand.opposite_vertices
        removed = set(cand.tetrahedra)
        kept = [t for t in self.tetrahedra if t not in removed]
        kept.extend(
            [
                norm_tet((u, w1, w2, w3)),
                norm_tet((v, w1, w2, w3)),
            ]
        )
        return Triangulation(kept)

    def best_descent_move(self) -> Optional[Move32Candidate]:
        cands = self.candidate_32_moves()
        if not cands:
            return None
        cands.sort(
            key=lambda c: (c.delta_phi, c.A + c.C, tuple(-x for x in c.edge)),
            reverse=True,
        )
        return cands[0]


def load_triangulation(path: str) -> Triangulation:
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    tetrahedra = data["tetrahedra"] if isinstance(data, dict) else data
    return Triangulation(tetrahedra)


def search_counterexample(path: str) -> int:
    T = load_triangulation(path)
    if not T.closed_pseudomanifold_faces():
        print(json.dumps({"status": "invalid", "reason": "not_closed_pseudomanifold"}))
        return 2

    cands = T.candidate_32_moves()
    witness = [c for c in cands if c.A + c.C >= 3]
    strict = [c for c in cands if c.delta_phi > 0]
    best = T.best_descent_move()

    payload = {
        "phi": T.phi(),
        "vertex_degrees": T.vertex_degrees(),
        "num_candidate_32": len(cands),
        "num_A_plus_C_ge_3": len(witness),
        "num_delta_phi_positive": len(strict),
        "best_move": None
        if best is None
        else {
            "edge": list(best.edge),
            "opposite_vertices": list(best.opposite_vertices),
            "A": best.A,
            "C": best.C,
            "A_plus_C": best.A + best.C,
            "delta_phi": best.delta_phi,
        },
        "lemma_B_prime_counterexample": bool(T.phi() > 0 and len(witness) == 0),
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 1 if payload["lemma_B_prime_counterexample"] else 0


def do_step(path: str, out: str) -> int:
    T = load_triangulation(path)
    best = T.best_descent_move()
    if best is None:
        print(json.dumps({"status": "no_move"}))
        return 1
    T2 = T.apply_32(best)
    payload = {
        "move": {
            "edge": list(best.edge),
            "opposite_vertices": list(best.opposite_vertices),
            "A": best.A,
            "C": best.C,
            "A_plus_C": best.A + best.C,
            "delta_phi_predicted": best.delta_phi,
        },
        "phi_before": T.phi(),
        "phi_after": T2.phi(),
        "strict_descent": T2.phi() < T.phi(),
        "tetrahedra": [list(t) for t in T2.tetrahedra],
    }
    with open(out, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["strict_descent"] else 2


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_scan = sub.add_parser("scan")
    p_scan.add_argument("input")

    p_step = sub.add_parser("step")
    p_step.add_argument("input")
    p_step.add_argument("output")

    args = parser.parse_args()

    if args.cmd == "scan":
        return search_counterexample(args.input)
    if args.cmd == "step":
        return do_step(args.input, args.output)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
