from collections import defaultdict, deque
from itertools import combinations

class Face:
    def __init__(self, verts):
        self.verts = tuple(sorted(verts))
    def __hash__(self):
        return hash(self.verts)
    def __eq__(self, other):
        return self.verts == other.verts
    def edges(self):
        return [tuple(sorted(e)) for e in combinations(self.verts, 2)]

class LinkComplex:
    def __init__(self, faces):
        self.F = list(dict.fromkeys(Face(f.verts if isinstance(f, Face) else f) for f in faces))
        self.E = sorted(set(e for f in self.F for e in f.edges()))
        self.V = sorted(set(v for f in self.F for v in f.verts))

def link_faces(L):
    return len(L.F)

def link_edges(L):
    return len(L.E)

def link_vertices(L):
    return len(L.V)

def euler_char(L):
    return link_vertices(L) - link_edges(L) + link_faces(L)

def edge_incidence_count(L):
    cnt = defaultdict(int)
    for f in L.F:
        for e in f.edges():
            cnt[e] += 1
    return cnt

def edge_two_faces(L):
    cnt = edge_incidence_count(L)
    return len(cnt) > 0 and all(v == 2 for v in cnt.values())

def build_adj(L):
    adj = defaultdict(set)
    for i, f in enumerate(L.F):
        fe = set(f.edges())
        for j, g in enumerate(L.F):
            if i == j:
                continue
            if fe & set(g.edges()):
                adj[i].add(j)
    return adj

def bfs_closure(L):
    if not L.F:
        return set()
    adj = build_adj(L)
    seen = {0}
    q = deque([0])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                q.append(v)
    return seen

def link_connected(L):
    return len(bfs_closure(L)) == len(L.F) and len(L.F) > 0

def incidences(L):
    return sum(3 for _ in L.F)

def incidence_face_count(L):
    return incidences(L) == 3 * link_faces(L)

def incidence_edge_count(L):
    if not edge_two_faces(L):
        return False
    return sum(edge_incidence_count(L).values()) == 2 * link_edges(L)

def edge_face_relation(L):
    if not edge_two_faces(L):
        return False
    return 2 * link_edges(L) == 3 * link_faces(L)

def is_sphere(L):
    return euler_char(L) == 2 and link_connected(L) and edge_two_faces(L)

def solve_counts(V, E, F):
    return (2 * E == 3 * F) and (V - E + F == 2)

def tetra_boundary():
    return LinkComplex([
        (0, 1, 2),
        (0, 1, 3),
        (0, 2, 3),
        (1, 2, 3),
    ])

def open_shell():
    return LinkComplex([
        (0, 1, 2),
        (0, 1, 3),
        (0, 2, 3),
    ])

def disconnected_pair():
    return LinkComplex([
        (0, 1, 2),
        (3, 4, 5),
    ])

def run_case(name, L, expect_sphere):
    print(f"CASE {name}")
    V, E, F = link_vertices(L), link_edges(L), link_faces(L)
    print(f"  counts: V={V}, E={E}, F={F}")
    print(f"  chi={euler_char(L)}")
    print(f"  connected={link_connected(L)}")
    print(f"  edge_two_faces={edge_two_faces(L)}")
    print(f"  incidence_face_count={incidence_face_count(L)}")
    print(f"  incidence_edge_count={incidence_edge_count(L)}")
    print(f"  edge_face_relation={edge_face_relation(L)}")
    print(f"  is_sphere={is_sphere(L)}")
    assert is_sphere(L) == expect_sphere
    if expect_sphere:
        assert F == 4
        assert edge_face_relation(L)
        assert solve_counts(V, E, F)
        assert V == 4 and E == 6 and F == 4
    print("  PASS")

def main():
    run_case("tetra_boundary", tetra_boundary(), True)
    run_case("open_shell", open_shell(), False)
    run_case("disconnected_pair", disconnected_pair(), False)
    print("ALL TESTS PASSED")

if __name__ == "__main__":
    main()
