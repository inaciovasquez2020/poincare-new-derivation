from itertools import combinations
from collections import defaultdict

class Face:
    def __init__(self, v): self.v = tuple(sorted(v))
    def edges(self): return [tuple(sorted(e)) for e in combinations(self.v,2)]

class Link:
    def __init__(self, faces):
        self.F = [Face(f.v) for f in faces]
        self.E = list({e for f in self.F for e in f.edges()})
        self.V = list({v for f in self.F for v in f.v})

def counts(L):
    return len(L.V), len(L.E), len(L.F)

def edge_two_faces(L):
    cnt = defaultdict(int)
    for f in L.F:
        for e in f.edges():
            cnt[e]+=1
    return all(v==2 for v in cnt.values())

def test_tetra_counts():
    L = Link([
        Face([0,1,2]),
        Face([0,1,3]),
        Face([0,2,3]),
        Face([1,2,3])
    ])
    V,E,F = counts(L)
    assert F==4
    assert 2*E == 3*F
    assert V - E + F == 2
    assert edge_two_faces(L)
    print("PASS: tetra counts consistent")

if __name__ == "__main__":
    test_tetra_counts()
    print("ALL TESTS PASSED")
