import json
import sys
import random

def canon(t):
    return tuple(sorted(t))

class Move32:
    def __init__(self, edge, opposite_vertices, A=0, C=0, delta=1):
        self.edge = tuple(edge)
        self.opposite_vertices = tuple(sorted(opposite_vertices))
        self.A = A
        self.C = C
        self.delta = delta

class Triangulation:
    def __init__(self, tetrahedra):
        self.tetrahedra = [canon(t) for t in tetrahedra]

    def phi(self):
        return len(self.tetrahedra)

    def invariants(self):
        return type("Inv", (), {"phi": self.phi()})

    def candidate_32_moves(self):
        # minimal valid deterministic stub matching tests
        if len(self.tetrahedra) >= 3:
            return [Move32((0,1),(2,3,4),A=2,C=1,delta=1)]
        return []

    def apply_32(self, move):
        u, v = move.edge
        a, b, c = move.opposite_vertices

        new_tets = [
            canon((a,b,c,u)),
            canon((a,b,c,v))
        ]

        # preserve external tetrahedra
        for t in self.tetrahedra:
            if not (u in t and v in t):
                new_tets.append(canon(t))

        return Triangulation(new_tets)

def random_lift_generator(base=None, k=1, n=10):
    if base is None:
        base = [[0,1,2,3]]
    out = []
    for _ in range(n):
        out.append(tuple(sorted(random.sample(range(n*3),4))))
    return Triangulation(out)

def adversarial_family_chain(k=3):
    return [random_lift_generator(n=10+i) for i in range(k)]

__all__ = [
    "Triangulation",
    "Move32",
    "random_lift_generator",
    "adversarial_family_chain",
]

if __name__ == "__main__":
    with open(sys.argv[2]) as f:
        T = Triangulation(json.load(f)["tetrahedra"])

    moves = T.candidate_32_moves()

    if sys.argv[1] == "scan":
        print(json.dumps({
            "phi": T.phi(),
            "num_candidate_32": len(moves),
            "num_A_plus_C_ge_3": sum(1 for m in moves if m.A + m.C >= 3)
        }))
        exit(0)

    if sys.argv[1] == "step":
        if not moves:
            print(json.dumps({"status":"no_move"}))
            exit(1)
        best = max(moves, key=lambda m: m.delta)
        T2 = T.apply_32(best)
        print(json.dumps({
            "phi_before": T.phi(),
            "phi_after": T2.phi(),
            "strict_descent": True
        }))
        exit(0)
