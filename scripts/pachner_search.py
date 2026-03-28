from __future__ import annotations

import json
import math
import random
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import combinations
from typing import Dict, List, Tuple


def canon(tets):
    return sorted(tuple(sorted(t)) for t in tets)


@dataclass
class Move32:
    edge: Tuple[int, int]
    opposite_vertices: Tuple[int, int, int]
    A: int
    C: int
    delta1: int
    delta2: int = 0

    @property
    def delta(self) -> int:
        return self.delta1


class Triangulation:
    def __init__(self, tetrahedra):
        self.tetrahedra: List[Tuple[int, ...]] = [
            tuple(sorted(t)) for t in tetrahedra
        ]

    def edge_to_tets(self) -> Dict[Tuple[int, int], List[Tuple]]:
        out: Dict[Tuple[int, int], List[Tuple]] = defaultdict(list)
        for t in self.tetrahedra:
            for e in combinations(t, 2):
                out[e].append(t)
        return dict(out)

    def vertex_degrees(self) -> Dict[int, int]:
        deg: Counter = Counter()
        for t in self.tetrahedra:
            for v in t:
                deg[v] += 1
        return dict(deg)

    def _edge_degrees(self) -> List[int]:
        return [len(ts) for ts in self.edge_to_tets().values()]

    def phi(self) -> int:
        return sum(d * (d - 1) // 2 for d in self._edge_degrees())

    def phi2(self) -> int:
        return sum(d * (d - 1) * (d - 2) // 6 for d in self._edge_degrees())

    def phi3(self) -> int:
        return sum(d * (d - 1) * (d - 2) * (d - 3) // 24
                   for d in self._edge_degrees())

    def phi4(self) -> int:
        return sum(d * (d - 1) * (d - 2) * (d - 3) * (d - 4) // 120
                   for d in self._edge_degrees())

    def entropy(self) -> float:
        degs = self._edge_degrees()
        total = sum(degs)
        if total == 0:
            return 0.0
        probs = [d / total for d in degs]
        return -sum(p * math.log(p) for p in probs if p > 0)

    def spectrum_penalty(self) -> int:
        return sum(max(0, d - 2) for d in self._edge_degrees())

    def candidate_32_moves(self) -> List[Move32]:
        edge_map = self.edge_to_tets()
        vdeg = self.vertex_degrees()
        phi_self = self.phi()
        phi2_self = self.phi2()
        out: List[Move32] = []

        for edge, tets in edge_map.items():
            if len(tets) != 3:
                continue
            u, v = edge

            opp_pairs = []
            valid = True
            for t in tets:
                rem = [x for x in t if x != u and x != v]
                if len(rem) != 2:
                    valid = False
                    break
                opp_pairs.append(frozenset(rem))
            if not valid:
                continue

            all_opp = set()
            for s in opp_pairs:
                all_opp |= s
            if len(all_opp) != 3:
                continue
            a, b, c = sorted(all_opp)

            expected = {frozenset({a, b}), frozenset({b, c}), frozenset({a, c})}
            if set(opp_pairs) != expected:
                continue

            T2 = self._apply_32_raw(edge, (a, b, c))
            delta1 = phi_self - T2.phi()
            delta2 = phi2_self - T2.phi2()

            A = vdeg.get(u, 0) - 2
            C = vdeg.get(v, 0) - 2

            out.append(Move32(
                edge=edge,
                opposite_vertices=(a, b, c),
                A=A,
                C=C,
                delta1=delta1,
                delta2=delta2,
            ))

        return out

    def positive_32_moves(self) -> List[Move32]:
        return [m for m in self.candidate_32_moves() if m.delta1 > 0]

    def zero_32_moves(self) -> List[Move32]:
        return [m for m in self.candidate_32_moves() if m.delta1 == 0]

    def _apply_32_raw(
        self,
        edge: Tuple[int, int],
        opposite_vertices: Tuple[int, int, int],
    ) -> "Triangulation":
        u, v = edge
        opp_set = set(opposite_vertices)

        to_remove = set()
        for t in self.tetrahedra:
            if u in t and v in t:
                rem = frozenset(x for x in t if x != u and x != v)
                if rem <= opp_set and len(rem) == 2:
                    to_remove.add(t)

        new_tets = [t for t in self.tetrahedra if t not in to_remove]
        a, b, c = sorted(opposite_vertices)
        new_tets.append(tuple(sorted([u, a, b, c])))
        new_tets.append(tuple(sorted([v, a, b, c])))
        return Triangulation(new_tets)

    def apply_32(self, move: Move32) -> "Triangulation":
        return self._apply_32_raw(move.edge, move.opposite_vertices)


def random_lift_generator(base_tets, lift_size: int, seed: int) -> Triangulation:
    rng = random.Random(seed)
    n = max(v for t in base_tets for v in t) + 1
    new_tets: List[List[int]] = []
    for i in range(lift_size):
        offset = i * n
        for t in base_tets:
            new_tets.append([v + offset for v in t])
    total_verts = n * lift_size
    perm = list(range(total_verts))
    indices = list(range(total_verts))
    rng.shuffle(indices)
    for idx in indices[:total_verts // 4]:
        target = rng.randint(0, total_verts - 1)
        perm[idx] = target
    glued = [[perm[v] for v in t] for t in new_tets]
    return Triangulation(glued)


def adversarial_family_chain(k: int) -> Triangulation:
    tets: List[List[int]] = []
    for i in range(k):
        base = i * 3
        apex_start = 1000 + i * 3
        for j in range(3):
            tets.append([base, base + 1, base + 2, apex_start + j])
    return Triangulation(tets)


def _cli() -> None:
    if len(sys.argv) < 3:
        print("Usage: pachner_search.py <cmd> <input.json> [output.json]",
              file=sys.stderr)
        raise SystemExit(1)

    cmd = sys.argv[1]
    with open(sys.argv[2], encoding="utf-8") as fh:
        data = json.load(fh)
    T = Triangulation(data["tetrahedra"])
    moves = T.candidate_32_moves()

    if cmd == "scan":
        print(json.dumps({
            "phi": T.phi(),
            "phi2": T.phi2(),
            "num_candidate_32": len(moves),
            "num_A_plus_C_ge_3": sum(1 for m in moves if m.A + m.C >= 3),
            "triples": [
                {"edge": list(m.edge), "A": m.A, "C": m.C,
                 "delta": m.delta1, "delta2": m.delta2}
                for m in moves
            ],
        }))
        raise SystemExit(0)

    if cmd == "find_zero_witness":
        witnesses = [
            {"edge": list(m.edge), "A": m.A, "C": m.C, "delta": m.delta1}
            for m in moves
            if m.A + m.C >= 3 and m.delta1 == 0
        ]
        print(json.dumps({
            "phi": T.phi(),
            "phi2": T.phi2(),
            "num_witnesses": len(witnesses),
            "witnesses": witnesses,
        }))
        raise SystemExit(0)

    if cmd == "step":
        pos = [m for m in moves if m.delta1 > 0]
        if not pos:
            print(json.dumps({"status": "no_move"}))
            raise SystemExit(1)
        best = max(pos, key=lambda m: (m.delta1, m.delta2))
        phi_before = T.phi()
        T2 = T.apply_32(best)
        phi_after = T2.phi()
        result = {
            "phi_before": phi_before,
            "phi_after": phi_after,
            "strict_descent": phi_after < phi_before,
        }
        if len(sys.argv) >= 4:
            with open(sys.argv[3], "w", encoding="utf-8") as fh:
                json.dump({"tetrahedra": [list(t) for t in T2.tetrahedra]}, fh)
        print(json.dumps(result))
        raise SystemExit(0)

    if cmd == "find_counterexample":
        bad = [
            {"edge": list(m.edge), "A": m.A, "C": m.C,
             "delta1": m.delta1, "delta2": m.delta2}
            for m in moves
            if m.A + m.C >= 3 and m.delta1 == 0
        ]
        print(json.dumps({
            "phi": T.phi(),
            "phi2": T.phi2(),
            "num_bad": len(bad),
            "bad": bad,
        }))
        raise SystemExit(0)

    print(f"Unknown command: {cmd}", file=sys.stderr)
    raise SystemExit(1)


if __name__ == "__main__":
    _cli()
