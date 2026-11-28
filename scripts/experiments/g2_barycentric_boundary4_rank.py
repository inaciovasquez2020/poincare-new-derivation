#!/usr/bin/env python3
"""Exact GF(2) rank audit for sd(boundary of 4-simplex), no dependencies."""
from itertools import combinations, permutations


def gf2_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def main():
    vertices = [frozenset(s) for k in range(1, 5)
                for s in combinations(range(5), k)]
    tetrahedra = {frozenset(frozenset(p[:k]) for k in range(1, 5))
                  for p in permutations(range(5))}
    faces = {frozenset(s) for t in tetrahedra for s in combinations(t, 3)}
    edges = {frozenset(s) for t in tetrahedra for s in combinations(t, 2)}
    vertices = sorted(vertices, key=lambda x: (len(x), tuple(sorted(x))))
    position = {v: i for i, v in enumerate(vertices)}
    key = lambda x: tuple(sorted(position[v] for v in x))
    edges = sorted(edges, key=key)
    faces = sorted(faces, key=key)
    tetrahedra = sorted(tetrahedra, key=key)
    V, E, F, T = map(len, (vertices, edges, faces, tetrahedra))
    assert (V, E, F, T) == (30, 150, 240, 120)
    delta0 = [sum(1 << i for i, v in enumerate(vertices) if v in e)
              for e in edges]
    delta1 = [sum(1 << i for i, e in enumerate(edges) if e <= f)
              for f in faces]
    dual = [sum(1 << i for i, f in enumerate(faces) if f <= t)
            for t in tetrahedra]
    ranks = (gf2_rank(delta0), gf2_rank(delta1), gf2_rank(dual))
    assert ranks == (29, 121, 119), ranks
    assert all(sum((row >> f) & 1 for row in dual) == 2
               for f in range(F))
    for e in range(E):
        fan = sum(1 << f for f, row in enumerate(delta1) if (row >> e) & 1)
        assert all((row & fan).bit_count() % 2 == 0 for row in dual)
    for v in range(V):
        coboundary = sum(1 << e for e, row in enumerate(delta0)
                         if (row >> v) & 1)
        assert all((row & coboundary).bit_count() % 2 == 0
                   for row in delta1)
    assert E - V + 1 == F - T + 1 == ranks[1]
    assert F == 2 * T and V - E + F - T == 0
    print('FIXTURE := sd_boundary_of_4_simplex')
    print(f'V={V} E={E} F={F} T={T}')
    print(f'RANK_D0={ranks[0]} RANK_PHI={ranks[1]} RANK_DUAL={ranks[2]}')
    print('FAN_BOUNDARIES_IN_DUAL_KERNEL := PASS')
    print('VERTEX_COBoundaries_IN_EDGE_COCYCLES := PASS')
    print('FAN_SPAN_EQUALS_DUAL_CYCLE_SPACE := PASS')
    print('G2_BARYCENTRIC_EXACT_RANK := PASS')


if __name__ == '__main__':
    main()
