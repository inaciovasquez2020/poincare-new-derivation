from collections import defaultdict, deque
from itertools import combinations

class Face:
    def __init__(self, verts):
        self.verts = tuple(sorted(verts))
    def edges(self):
        return [tuple(sorted(e)) for e in combinations(self.verts, 2)]
    def __eq__(self, other):
        return self.verts == other.verts
    def __hash__(self):
        return hash(self.verts)

class LinkComplex:
    def __init__(self, faces):
        self.faces = list({Face(f.verts) for f in faces})
        self.vertices = sorted({v for f in self.faces for v in f.verts})
        self.edges = list({e for f in self.faces for e in f.edges()})

def euler_char(L):
    return len(L.vertices) - len(L.edges) + len(L.faces)

def edge_incidence(L):
    count = defaultdict(int)
    for f in L.faces:
        for e in f.edges():
            count[e] += 1
    return count

def edge_two_faces(L):
    return all(v == 2 for v in edge_incidence(L).values())

def is_connected(L):
    if not L.faces:
        return False
    adj = defaultdict(set)
    for f in L.faces:
        for g in L.faces:
            if f != g and any(e in g.edges() for e in f.edges()):
                adj[f].add(g)
    visited = set()
    q = deque([L.faces[0]])
    while q:
        x = q.popleft()
        if x in visited:
            continue
        visited.add(x)
        q.extend(adj[x])
    return len(visited) == len(L.faces)

def is_sphere(L):
    return euler_char(L) == 2 and edge_two_faces(L) and is_connected(L)

def tetra_sphere():
    return LinkComplex([
        Face([0,1,2]),
        Face([0,1,3]),
        Face([0,2,3]),
        Face([1,2,3])
    ])

def test_sphere():
    L = tetra_sphere()
    assert is_sphere(L)
    print("PASS: tetra sphere")

def test_non_sphere():
    L = LinkComplex([
        Face([0,1,2]),
        Face([0,1,3]),
        Face([0,2,3])
    ])
    assert not is_sphere(L)
    print("PASS: non-sphere detected")

if __name__ == "__main__":
    test_sphere()
    test_non_sphere()
    print("ALL TESTS PASSED")
