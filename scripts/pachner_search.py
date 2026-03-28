from __future__ import annotations
import json
import math
import random
from itertools import combinations
from collections import defaultdict, Counter
from dataclasses import dataclass
from typing import List, Tuple, Dict, Iterable

Vertex = int
Tet = Tuple[int, int, int, int]
Edge = Tuple[int, int]

def norm_tet(t: Iterable[int]) -> Tet:
    return tuple(sorted(int(x) for x in t))

def norm_edge(a: int, b: int) -> Edge:
    return (a, b) if a < b else (b, a)

@dataclass
class Move32:
    edge: Edge
    opposite_vertices: Tuple[int, int, int]
    incident_tets: Tuple[Tet, Tet, Tet]
    A: int
    C: int
    delta1: int
    delta2: int
    delta3: int
    delta4: int
    deltaH: float
    deltaS: int

class Triangulation:
    def __init__(self, tetrahedra):
        self.tetrahedra = [norm_tet(t) for t in tetrahedra]
        self.vertices = sorted({v for t in self.tetrahedra for v in t})

    def vertex_degrees(self) -> Dict[Vertex, int]:
        deg = {v: 0 for v in self.vertices}
        for t in self.tetrahedra:
            for v in t:
                deg[v] += 1
        return deg

    def edge_to_tets(self):
        e2t = defaultdict(list)
        for t in self.tetrahedra:
            for a, b in combinations(t, 2):
                e2t[norm_edge(a, b)].append(t)
        return e2t

    def edge_degrees(self) -> Dict[Edge, int]:
        return {e: len(ts) for e, ts in self.edge_to_tets().items()}

    def phi(self) -> int:
        deg = self.vertex_degrees()
        return sum(abs(d - 6) for d in deg.values())

    def phi2(self) -> int:
        deg = self.vertex_degrees()
        return sum((d - 6) ** 2 for d in deg.values())

    def phi3(self) -> int:
        deg = self.vertex_degrees()
        return sum(abs(d - 6) ** 3 for d in deg.values())

    def phi4(self) -> int:
        deg = self.vertex_degrees()
        return sum(abs(d - 6) ** 4 for d in deg.values())

    def entropy(self) -> float:
        deg = self.vertex_degrees()
        n = len(deg)
        if n == 0:
            return 0.0
        hist = Counter(deg.values())
        out = 0.0
        for c in hist.values():
            p = c / n
            out -= p * math.log(p)
        return out

    def spectrum_penalty(self) -> int:
        edeg = self.edge_degrees()
        return sum(abs(k - 3) for k in edeg.values())

    def candidate_32_moves(self) -> List[Move32]:
        deg = self.vertex_degrees()
        edeg_before = self.edge_degrees()
        out: List[Move32] = []

        for (u, v), incident in self.edge_to_tets().items():
            if len(incident) != 3:
                continue

            incident = tuple(norm_tet(t) for t in incident)
            opp_sets = [tuple(sorted(set(t) - {u, v})) for t in incident]
            union = sorted({x for s in opp_sets for x in s})
            if len(union) != 3:
                continue

            w1, w2, w3 = union
            required = {
                norm_tet((u, v, w1, w2)),
                norm_tet((u, v, w1, w3)),
                norm_tet((u, v, w2, w3)),
            }
            if set(incident) != required:
                continue

            A = int(deg[u] > 6) + int(deg[v] > 6)
            C = sum(int(deg[w] < 6) for w in (w1, w2, w3))

            verts = (u, v, w1, w2, w3)

            before1 = sum(abs(deg[x] - 6) for x in verts)
            after1 = (
                abs((deg[u] - 3) - 6) +
                abs((deg[v] - 3) - 6) +
                abs((deg[w1] - 1) - 6) +
                abs((deg[w2] - 1) - 6) +
                abs((deg[w3] - 1) - 6)
            )

            before2 = sum((deg[x] - 6) ** 2 for x in verts)
            after2 = (
                ((deg[u] - 3) - 6) ** 2 +
                ((deg[v] - 3) - 6) ** 2 +
                ((deg[w1] - 1) - 6) ** 2 +
                ((deg[w2] - 1) - 6) ** 2 +
                ((deg[w3] - 1) - 6) ** 2
            )

            before3 = sum(abs(deg[x] - 6) ** 3 for x in verts)
            after3 = (
                abs((deg[u] - 3) - 6) ** 3 +
                abs((deg[v] - 3) - 6) ** 3 +
                abs((deg[w1] - 1) - 6) ** 3 +
                abs((deg[w2] - 1) - 6) ** 3 +
                abs((deg[w3] - 1) - 6) ** 3
            )

            before4 = sum(abs(deg[x] - 6) ** 4 for x in verts)
            after4 = (
                abs((deg[u] - 3) - 6) ** 4 +
                abs((deg[v] - 3) - 6) ** 4 +
                abs((deg[w1] - 1) - 6) ** 4 +
                abs((deg[w2] - 1) - 6) ** 4 +
                abs((deg[w3] - 1) - 6) ** 4
            )

            T2 = self.apply_32_raw((u, v), (w1, w2, w3), incident)
            deltaH = T2.entropy() - self.entropy()
            deltaS = self.spectrum_penalty() - T2.spectrum_penalty()

            out.append(
                Move32(
                    (u, v),
                    (w1, w2, w3),
                    incident,
                    A,
                    C,
                    before1 - after1,
                    before2 - after2,
                    before3 - after3,
                    before4 - after4,
                    deltaH,
                    deltaS,
                )
            )

        return out

    def positive_32_moves(self):
        return [m for m in self.candidate_32_moves() if m.delta1 > 0]

    def zero_32_moves(self):
        return [m for m in self.candidate_32_moves() if m.delta1 == 0]

    def apply_32_raw(self, edge: Edge, opposite_vertices: Tuple[int, int, int], incident_tets: Tuple[Tet, Tet, Tet]):
        current = set(self.tetrahedra)
        remove = set(incident_tets)
        remaining = current - remove

        u, v = edge
        w1, w2, w3 = opposite_vertices
        new = {
            norm_tet((u, w1, w2, w3)),
            norm_tet((v, w1, w2, w3)),
        }

        return Triangulation(list(remaining | new))

    def apply_32(self, move: Move32):
        return self.apply_32_raw(move.edge, move.opposite_vertices, move.incident_tets)

    def best_lex_move(self):
        moves = self.candidate_32_moves()
        if not moves:
            return None

        admissible = [
            m for m in moves
            if (m.delta1, m.delta2, m.delta3, m.delta4, m.deltaH, m.deltaS) > (0, 0, 0, 0, float("-inf"), float("-inf"))
        ]

        pos1 = [m for m in admissible if m.delta1 > 0]
        pos2 = [m for m in admissible if m.delta1 == 0 and m.delta2 > 0]
        pos3 = [m for m in admissible if m.delta1 == 0 and m.delta2 == 0 and m.delta3 > 0]
        pos4 = [m for m in admissible if m.delta1 == 0 and m.delta2 == 0 and m.delta3 == 0 and m.delta4 > 0]
        ent  = [m for m in admissible if m.delta1 == 0 and m.delta2 == 0 and m.delta3 == 0 and m.delta4 == 0 and m.deltaH > 0]
        spec = [m for m in admissible if m.delta1 == 0 and m.delta2 == 0 and m.delta3 == 0 and m.delta4 == 0 and m.deltaH <= 0 and m.deltaS > 0]

        candidates = pos1 if pos1 else pos2 if pos2 else pos3 if pos3 else pos4 if pos4 else ent if ent else spec
        if not candidates:
            return None

        return max(
            candidates,
            key=lambda m: (m.delta1, m.delta2, m.delta3, m.delta4, m.deltaH, m.deltaS, m.A + m.C),
        )

def load(path):
    with open(path) as f:
        return Triangulation(json.load(f)["tetrahedra"])

def tetra_pool(n_vertices: int):
    verts = list(range(n_vertices))
    return [norm_tet(t) for t in combinations(verts, 4)]

def enumerate_small_triangulations(n_vertices: int, num_tets: int, limit: int):
    pool = tetra_pool(n_vertices)
    count = 0
    for family in combinations(pool, num_tets):
        yield Triangulation(family)
        count += 1
        if count >= limit:
            return

def random_lift_generator(base_tets, lift_size: int, seed: int):
    rng = random.Random(seed)
    base_tets = [norm_tet(t) for t in base_tets]
    lifted = []
    for tet in base_tets:
        choices = [rng.randrange(lift_size) for _ in range(4)]
        lifted.append(tuple(v * lift_size + choices[i] for i, v in enumerate(tet)))
    return Triangulation(lifted)

def adversarial_family_chain(n: int):
    out = []
    top = 1000
    for i in range(n):
        out.append(norm_tet((0, 1, 2, top + 3 * i)))
        out.append(norm_tet((0, 1, 3, top + 3 * i + 1)))
        out.append(norm_tet((0, 2, 3, top + 3 * i + 2)))
    return Triangulation(out)

def move_payload(m: Move32):
    return {
        "edge": list(m.edge),
        "opposite_vertices": list(m.opposite_vertices),
        "A": m.A,
        "C": m.C,
        "delta": m.delta1,
        "delta2": m.delta2,
        "delta3": m.delta3,
        "delta4": m.delta4,
        "deltaH": m.deltaH,
        "deltaS": m.deltaS,
    }

def non_descent_payload(T: Triangulation):
    return {
        "phi": T.phi(),
        "phi2": T.phi2(),
        "phi3": T.phi3(),
        "phi4": T.phi4(),
        "entropy": T.entropy(),
        "spectrum_penalty": T.spectrum_penalty(),
        "num_tetrahedra": len(T.tetrahedra),
        "tetrahedra": [list(t) for t in sorted(T.tetrahedra)],
    }

if __name__ == "__main__":
    import sys

    cmd = sys.argv[1]

    if cmd == "scan":
        T = load(sys.argv[2])
        moves = T.candidate_32_moves()
        print(json.dumps({
            "phi": T.phi(),
            "phi2": T.phi2(),
            "phi3": T.phi3(),
            "phi4": T.phi4(),
            "entropy": T.entropy(),
            "spectrum_penalty": T.spectrum_penalty(),
            "triples": [
                {
                    "edge": list(m.edge),
                    "A": m.A,
                    "C": m.C,
                    "delta": m.delta1,
                    "delta2": m.delta2,
                    "delta3": m.delta3,
                    "delta4": m.delta4,
                    "deltaH": m.deltaH,
                    "deltaS": m.deltaS,
                }
                for m in moves
            ]
        }))
        raise SystemExit(0)

    if cmd == "find_zero_witness":
        T = load(sys.argv[2])
        moves = T.candidate_32_moves()
        bad = [
            {
                "edge": list(m.edge),
                "A": m.A,
                "C": m.C,
                "delta": m.delta1,
                "delta2": m.delta2,
                "delta3": m.delta3,
                "delta4": m.delta4,
                "deltaH": m.deltaH,
                "deltaS": m.deltaS,
            }
            for m in moves if (m.A + m.C >= 3 and m.delta1 == 0 and m.delta2 == 0 and m.delta3 == 0 and m.delta4 == 0)
        ]
        print(json.dumps({
            "phi": T.phi(),
            "phi2": T.phi2(),
            "phi3": T.phi3(),
            "phi4": T.phi4(),
            "num_witnesses": len(bad),
            "witnesses": bad
        }))
        raise SystemExit(0)

    if cmd == "step":
        T = load(sys.argv[2])
        seq = []
        steps = 0
        while True:
            move = T.best_lex_move()
            if move is None:
                break
            T2 = T.apply_32(move)
            seq.append({
                "phi_before": T.phi(),
                "phi_after": T2.phi(),
                "phi2_before": T.phi2(),
                "phi2_after": T2.phi2(),
                "phi3_before": T.phi3(),
                "phi3_after": T2.phi3(),
                "phi4_before": T.phi4(),
                "phi4_after": T2.phi4(),
                "entropy_before": T.entropy(),
                "entropy_after": T2.entropy(),
                "spectrum_before": T.spectrum_penalty(),
                "spectrum_after": T2.spectrum_penalty(),
                "move": move_payload(move),
            })
            if (T2.phi(), T2.phi2(), T2.phi3(), T2.phi4(), T2.entropy(), -T2.spectrum_penalty()) <= \
               (T.phi(), T.phi2(), T.phi3(), T.phi4(), T.entropy(), -T.spectrum_penalty()):
                break
            T = T2
            steps += 1
            if steps > 100:
                break
        print(json.dumps({
            "steps": steps,
            "final_phi": T.phi(),
            "final_phi2": T.phi2(),
            "final_phi3": T.phi3(),
            "final_phi4": T.phi4(),
            "final_entropy": T.entropy(),
            "final_spectrum_penalty": T.spectrum_penalty(),
            "sequence": seq
        }))
        raise SystemExit(0)

    if cmd == "enumerate_small":
        n_vertices = int(sys.argv[2])
        num_tets = int(sys.argv[3])
        limit = int(sys.argv[4])
        best = None
        for T in enumerate_small_triangulations(n_vertices, num_tets, limit):
            if T.best_lex_move() is None:
                payload = non_descent_payload(T)
                key = (
                    payload["num_tetrahedra"],
                    payload["phi4"],
                    payload["phi3"],
                    payload["phi2"],
                    payload["phi"],
                    payload["spectrum_penalty"],
                    -payload["entropy"],
                )
                if best is None or key < (
                    best["num_tetrahedra"],
                    best["phi4"],
                    best["phi3"],
                    best["phi2"],
                    best["phi"],
                    best["spectrum_penalty"],
                    -best["entropy"],
                ):
                    best = payload
        print(json.dumps({
            "searched_limit": limit,
            "n_vertices": n_vertices,
            "num_tets": num_tets,
            "minimal_non_descent": best
        }))
        raise SystemExit(0)

    if cmd == "random_lift":
        base_path = sys.argv[2]
        lift_size = int(sys.argv[3])
        seed = int(sys.argv[4])
        with open(base_path) as f:
            base = json.load(f)["tetrahedra"]
        T = random_lift_generator(base, lift_size, seed)
        print(json.dumps({
            "lift_size": lift_size,
            "seed": seed,
            "phi": T.phi(),
            "phi2": T.phi2(),
            "phi3": T.phi3(),
            "phi4": T.phi4(),
            "entropy": T.entropy(),
            "spectrum_penalty": T.spectrum_penalty(),
            "num_tetrahedra": len(T.tetrahedra),
            "sample_tetrahedra": [list(t) for t in sorted(T.tetrahedra)[:10]]
        }))
        raise SystemExit(0)

    if cmd == "adversarial":
        n = int(sys.argv[2])
        T = adversarial_family_chain(n)
        print(json.dumps(non_descent_payload(T)))
        raise SystemExit(0)
