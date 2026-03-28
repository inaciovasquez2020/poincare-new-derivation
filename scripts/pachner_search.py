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
    delta1: int
    delta2: int

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

    def phi2(self):
        deg = self.vertex_degrees()
        return sum((d-6)**2 for d in deg.values())

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

            before1 = sum(abs(deg[x]-6) for x in (u,v,w1,w2,w3))
            after1  = (
                abs((deg[u]-3)-6)+
                abs((deg[v]-3)-6)+
                abs((deg[w1]-1)-6)+
                abs((deg[w2]-1)-6)+
                abs((deg[w3]-1)-6)
            )

            before2 = sum((deg[x]-6)**2 for x in (u,v,w1,w2,w3))
            after2  = (
                ((deg[u]-3)-6)**2+
                ((deg[v]-3)-6)**2+
                ((deg[w1]-1)-6)**2+
                ((deg[w2]-1)-6)**2+
                ((deg[w3]-1)-6)**2
            )

            out.append(Move32((u,v),(w1,w2,w3),incident,A,C,before1-after1,before2-after2))

        return out

    def positive_32_moves(self):
        return [m for m in self.candidate_32_moves() if m.delta1 > 0]

    def zero_32_moves(self):
        return [m for m in self.candidate_32_moves() if m.delta1 == 0]

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

    def best_lex_move(self):
        moves = self.candidate_32_moves()
        pos = [m for m in moves if m.delta1 > 0]
        weak = [m for m in moves if m.delta1 == 0 and m.delta2 > 0]

        candidates = pos if pos else weak
        if not candidates:
            return None

        return max(candidates, key=lambda m:(m.delta1,m.delta2,m.A+m.C))

def load(path):
    with open(path) as f:
        return Triangulation(json.load(f)["tetrahedra"])

if __name__=="__main__":
    import sys
    cmd = sys.argv[1]
    T = load(sys.argv[2])

    if cmd == "scan":
        moves = T.candidate_32_moves()
        print(json.dumps({
            "phi":T.phi(),
            "phi2":T.phi2(),
            "triples":[
                {"edge":list(m.edge),"A":m.A,"C":m.C,"delta":m.delta1}
                for m in moves
            ]
        }))
        exit(0)

    if cmd == "find_zero_witness":
        moves = T.candidate_32_moves()
        bad = [
            {"edge":list(m.edge),"A":m.A,"C":m.C,"delta":m.delta1}
            for m in moves if (m.A+m.C>=3 and m.delta1==0)
        ]
        print(json.dumps({
            "phi":T.phi(),
            "phi2":T.phi2(),
            "num_bad":len(bad),
            "bad":bad
        }))
        exit(0)
