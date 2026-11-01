#!/usr/bin/env python3
"""Finite negative test: anchored two-fan return need not force Move23.

One connected closed combinatorial 3-manifold on nine vertices, with
beta_1(F_2)=1 and no legal Move23, supports a different-transverse
oriented two-step fan return. This is NOT a simply connected example.

The external defect-minimality argument uses the Novik-Swartz bound
g2 >= 10 * beta_1(F_2) for closed connected homology 3-manifolds:
Lutz, Sulanke and Swartz, f-Vectors of 3-Manifolds (2009),
https://doi.org/10.37236/79 . This script does not prove that theorem.
No Lean result or global JIID conclusion is asserted.
"""
from collections import Counter
from itertools import combinations
import hashlib
import json

N = 9
STARTERS = ((0, 1, 2, 4), (0, 1, 2, 7), (0, 1, 3, 4))
TETS = frozenset(
    frozenset((v + shift) % N for v in tet)
    for tet in STARTERS for shift in range(N)
)

def faces(tet, size):
    return (frozenset(f) for f in combinations(sorted(tet), size))

def connected(vertices, edges):
    graph = {v: set() for v in vertices}
    for edge in edges:
        a, b = tuple(edge)
        graph[a].add(b)
        graph[b].add(a)
    seen = set()
    pending = [next(iter(vertices))]
    while pending:
        v = pending.pop()
        if v not in seen:
            seen.add(v)
            pending.extend(graph[v] - seen)
    return seen == vertices

def rank_f2(vectors):
    basis = {}
    for column in vectors:
        while column:
            pivot = column.bit_length() - 1
            if pivot in basis:
                column ^= basis[pivot]
            else:
                basis[pivot] = column
                break
    return len(basis)

VERTICES = frozenset().union(*TETS)
EDGES = frozenset(e for tet in TETS for e in faces(tet, 2))
TRI_COUNT = Counter(f for tet in TETS for f in faces(tet, 3))
EDGE_COUNT = Counter(e for tet in TETS for e in faces(tet, 2))
VERTEX_DEGREE = Counter(v for tet in TETS for v in tet)

assert len(TETS) == 27 and len(VERTICES) == 9
assert len(EDGES) == 36 and len(TRI_COUNT) == 54
assert set(TRI_COUNT.values()) == {2}
assert set(VERTEX_DEGREE.values()) == {12}
assert all(frozenset(p) in EDGES for p in combinations(range(N), 2))

# The vertex links are closed, connected combinatorial 2-spheres.
for center in VERTICES:
    link = frozenset(frozenset(tet - {center}) for tet in TETS if center in tet)
    vertices = frozenset().union(*link)
    edges = frozenset(e for tri in link for e in faces(tri, 2))
    counts = Counter(e for tri in link for e in faces(tri, 2))
    assert set(counts.values()) == {2}
    assert connected(vertices, edges)
    assert len(vertices) - len(edges) + len(link) == 2
    for vertex in vertices:
        circle = [frozenset(tri - {vertex}) for tri in link if vertex in tri]
        circle_vertices = frozenset().union(*circle)
        degrees = Counter(v for edge in circle for v in edge)
        assert set(degrees.values()) == {2}
        assert connected(circle_vertices, circle)

edge_index = {
    tuple(sorted(e)): i
    for i, e in enumerate(sorted(EDGES, key=lambda e: tuple(sorted(e))))
}
boundary2 = [
    sum(1 << edge_index[tuple(sorted(e))] for e in faces(tri, 2))
    for tri in TRI_COUNT
]
beta1_f2 = len(EDGES) - (len(VERTICES) - 1) - rank_f2(boundary2)
assert beta1_f2 == 1  # Therefore the manifold is not simply connected.

# Exhaust legal 2->3 candidates under the repository's LegalIn predicate.
legal23 = 0
for tri, face_count in TRI_COUNT.items():
    assert face_count == 2
    incident = [tet for tet in TETS if tri <= tet]
    assert len(incident) == 2
    opposite = frozenset(next(iter(tet - tri)) for tet in incident)
    assert len(opposite) == 2
    if opposite not in EDGES:
        legal23 += 1
assert legal23 == 0

v, x, z0, z1, y0, y1 = 0, 1, 2, 3, 4, 8
left0 = frozenset((v, x, y0, z0))
right0 = frozenset((v, x, y0, z1))
witness0 = frozenset((v, z0, z1, y1))
left1 = witness0  # Successor is anchored at the incoming witness.
right1 = frozenset((x, z0, z1, y1))
witness1 = left0
assert len({v, x, z0, z1, y0, y1}) == 6
assert {left0, right0, witness0, left1, right1, witness1} <= TETS
assert left0 & right0 == frozenset((v, x, y0))
assert left1 & right1 == frozenset((z0, z1, y1))
assert {z0, z1} <= witness0 and not ({v, x} <= witness0)
assert {v, x} <= witness1 and not ({z0, z1} <= witness1)
assert y0 != y1
assert EDGE_COUNT[frozenset((v, x))] == 6
assert EDGE_COUNT[frozenset((z0, z1))] == 6

phi = sum(VERTEX_DEGREE[v] - 4 for v in VERTICES)
assert phi == 72 == 4 * len(EDGES) - 8 * len(VERTICES)

# Conditional external conclusion: beta1=1 implies g2>=10; every
# homeomorphic closed 3-manifold triangulation L therefore has f1>=4*f0.
# Combined with f1<=binom(f0,2), f0>=9, so PhiSupport(L)>=72.
receipt = {
    "f_vector": [len(VERTICES), len(EDGES), len(TRI_COUNT), len(TETS)],
    "beta1_f2": beta1_f2,
    "PhiSupport": phi,
    "legal_Move23": legal23,
    "old_edge": [v, x], "successor_edge": [z0, z1],
    "transverse": [y0, y1],
    "edge_tet_incidence": [EDGE_COUNT[frozenset((v, x))],
                           EDGE_COUNT[frozenset((z0, z1))]],
    "incoming_witness": sorted(witness0),
    "anchored_successor_left_tet": sorted(left1),
    "facet_sha256": hashlib.sha256(
        json.dumps(sorted(sorted(t) for t in TETS), separators=(",", ":")).encode()
    ).hexdigest(),
    "minimality": "external theorem, not computer or Lean verified",
    "JIID": "OPEN",
}
print(json.dumps(receipt, indent=2))
