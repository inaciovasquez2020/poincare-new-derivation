#!/usr/bin/env python3
"""Exact finite tests of grid-vertex cancellation; not a topology or Lean checker."""
from itertools import combinations, product
from pathlib import Path
import json


def audit(facets, nx, ny):
    vertices = sorted(set().union(*map(set, facets)))
    edges = sorted({e for f in facets for e in combinations(sorted(f), 2)})
    bits = {e: 1 << i for i, e in enumerate(edges)}
    def edge(a, b):
        return 0 if a == b else bits[tuple(sorted((a, b)))]
    def word(seq):
        value = 0
        for a, b in zip(seq, seq[1:]):
            value ^= edge(a, b)
        return value
    triangles = [word((*f, f[0])) for f in facets]
    weights = [w for w in range(1 << len(edges))
               if all((w & t).bit_count() % 2 == 0 for t in triangles)]
    exact = {sum(((a >> u ^ a >> v) & 1) * bits[u, v] for u, v in edges)
             for a in range(1 << len(vertices))}
    assert exact <= set(weights)
    index = lambda i, j: i * (ny + 1) + j
    cells = [(index(i,j), index(i+1,j), index(i+1,j+1), index(i,j+1))
             for i in range(nx) for j in range(ny)]
    perimeter = ([index(i,0) for i in range(nx+1)] +
                 [index(nx,j) for j in range(1,ny+1)] +
                 [index(i,ny) for i in range(nx-1,-1,-1)] +
                 [index(0,j) for j in range(ny-1,-1,-1)])
    allowed = {tuple(c) for c in product(vertices, repeat=4)
               if any(set(c) <= set(f) for f in facets)}
    tested = compatible = pairings = active = nonexact_pairings = 0
    for lab in product(vertices, repeat=(nx+1)*(ny+1)):
        tested += 1
        if not all(tuple(lab[k] for k in cell) in allowed for cell in cells):
            continue
        compatible += 1
        boundary = word([lab[k] for k in perimeter])
        total = 0
        for cell in cells:
            a,b,c,d = (lab[k] for k in cell)
            # Independent triangulation of the cell into two triangles.
            total ^= word([a,b,c,a]) ^ word([a,c,d,a])
        assert total == boundary
        for w in weights:
            assert (w & boundary).bit_count() % 2 == 0
            pairings += 1
            nonexact_pairings += w not in exact
        base = lab[index(0,0)]
        if all(lab[index(i,j)] == base for i,j in
               [(i,0) for i in range(nx+1)] + [(i,ny) for i in range(nx+1)] + [(nx,j) for j in range(ny+1)]):
            active += 1
            assert word([lab[index(0,j)] for j in range(ny+1)]) == boundary
    return dict(grid=[nx,ny], assignments=tested, compatible=compatible,
                cocycles=len(weights), exact_cocycles=len(exact), pairings=pairings,
                nonexact_cocycle_pairings=nonexact_pairings,
                three_constant_sides=active, mismatches=0)


def word_audit():
    checks = 0
    for n in range(1,13):
        for seq in product(range(2), repeat=n+1):
            for weight in (0,1):
                got = sum(weight * (a != b) for a,b in zip(seq,seq[1:])) % 2
                assert got == weight * (seq[0] != seq[-1])
                checks += 1
    return checks

if __name__ == '__main__':
    # Triangular disk with two facets, and a six-vertex triangular annulus.
    disk = [(0,1,2),(1,2,3)]
    annulus = [(i,(i+1)%3,3+(i+1)%3) for i in range(3)] + [(i,3+i,3+(i+1)%3) for i in range(3)]
    # Pairwise edge compatibility alone is insufficient: 3-cycle, no triangle,
    # cell corners 0,1,2,0, with one edge of odd weight.
    corners = [0,1,2,0]
    graph_edges = {(0,1),(0,2),(1,2)}
    pairwise = all(e in graph_edges for e in combinations(sorted(set(corners)), 2))
    common = any(set(corners) <= set(e) for e in graph_edges)
    odd = sum(tuple(sorted((a,b))) == (0,1)
              for a,b in zip(corners, corners[1:] + corners[:1])) % 2
    assert pairwise and not common and odd == 1
    negative = dict(corners=corners, pairwise_edges_present=pairwise,
                    common_simplex=common, boundary_parity=odd)
    receipt = dict(status='COMPUTATION_PASS', disk=audit(disk,2,2),
                   annulus=audit(annulus,1,2), two_label_word_checks=word_audit(),
                   pairwise_only_negative_control=negative,
                   scope='Finite algebraic grid and word checks only; no Lean or geometric homotopy verification.')
    print(json.dumps(receipt, indent=2))
