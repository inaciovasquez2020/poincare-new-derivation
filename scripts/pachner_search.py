from __future__ import annotations
import json
from itertools import combinations
from collections import defaultdict
from dataclasses import dataclass
from typing import List, Tuple

Vertex = int
Tet = Tuple[int,int,int,int]
Edge = Tuple[int,int]

def norm_tet(t):
    return tuple(sorted(t))

def norm_edge(a,b):
    return (a,b) if a<b else (b,a)

@dataclass
class Move32:
    edge: Edge
    opposite_vertices: Tuple[int,int,int]
    incident_tets: Tuple[Tet,Tet,Tet]
    A: int
    C: int
    delta: int

class Triangulation:
    def __init__(self, tetrahedra):
        self.tetrahedra = [norm_tet(t) for t in tetrahedra]
        self.vertices = sorted({v for t in self.tetrahedra for v in t})

    def vertex_degrees(self):
        deg = {v:0 for v in self.vertices}
        for t in self.tetrahedra:
            for v in t:
                deg[v]+=1
        return deg

    def phi(self):
        deg = self.vertex_degrees()
        return sum(abs(d-6) for d in deg.values())

    def edge_to_tets(self):
        e2t = defaultdict(list)
        for t in self.tetrahedra:
            for a,b in combinations(t,2):
                e2t[norm_edge(a,b)].append(t)
        return e2t

    def candidate_32_moves(self) -> List[Move32]:
        deg = self.vertex_degrees()
        out = []
        for (u,v), incident in self.edge_to_tets().items():
            if len(incident)!=3:
                continue

            incident = tuple(norm_tet(t) for t in incident)

            opp_sets = [tuple(sorted(set(t)-{u,v})) for t in incident]
            union = sorted({x for s in opp_sets for x in s})
            if len(union)!=3:
                continue

            w1,w2,w3 = union

            required = {
                norm_tet((u,v,w1,w2)),
                norm_tet((u,v,w1,w3)),
                norm_tet((u,v,w2,w3)),
            }
            if set(incident)!=required:
                continue

            A = int(deg[u]>6)+int(deg[v]>6)
            C = sum(int(deg[w]<6) for w in (w1,w2,w3))

            before = sum(abs(deg[x]-6) for x in (u,v,w1,w2,w3))
            after  = (
                abs((deg[u]-3)-6)+
                abs((deg[v]-3)-6)+
                abs((deg[w1]-1)-6)+
                abs((deg[w2]-1)-6)+
                abs((deg[w3]-1)-6)
            )

            out.append(Move32((u,v),(w1,w2,w3),incident,A,C,before-after))

        return out

    def apply_32(self, move: Move32):
        current = set(self.tetrahedra)
        remove = set(move.incident_tets)

        remaining = current - remove

        u,v = move.edge
        w1,w2,w3 = move.opposite_vertices

        new = {
            norm_tet((u,w1,w2,w3)),
            norm_tet((v,w1,w2,w3)),
        }

        return Triangulation(list(remaining | new))

if __name__=="__main__":
    import sys
    data = json.load(open(sys.argv[2]))
    T = Triangulation(data["tetrahedra"])
    moves = T.candidate_32_moves()

    if sys.argv[1]=="scan":
        print(json.dumps({
            "phi":T.phi(),
            "num_candidate_32":len(moves),
            "num_A_plus_C_ge_3":sum(1 for m in moves if m.A+m.C>=3)
        }))
        exit(0)

    if sys.argv[1]=="step":
        if not moves:
            print(json.dumps({"status":"no_move"}))
            exit(1)
        best = max(moves, key=lambda m:m.delta)
        T2 = T.apply_32(best)
        print(json.dumps({
            "phi_before":T.phi(),
            "phi_after":T2.phi(),
            "strict_descent":T2.phi()<T.phi()
        }))
        exit(0)
