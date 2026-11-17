#!/usr/bin/env python3
"""Exhaustive F2 incidence audit for the boundary of the 4-simplex."""
from itertools import combinations


def subsets(n, k):
    return [frozenset(x) for x in combinations(range(n), k)]


def rank(rows, ncols):
    rows = list(rows)
    pivot_row = 0
    for col in range(ncols):
        p = next((j for j in range(pivot_row, len(rows))
                  if rows[j] & (1 << col)), None)
        if p is None:
            continue
        rows[pivot_row], rows[p] = rows[p], rows[pivot_row]
        for j in range(len(rows)):
            if j != pivot_row and rows[j] & (1 << col):
                rows[j] ^= rows[pivot_row]
        pivot_row += 1
    return pivot_row


def eval_rows(rows, vector):
    return sum((((row & vector).bit_count() & 1) << i)
               for i, row in enumerate(rows))


def main():
    vertices = subsets(5, 1)
    edges = subsets(5, 2)
    faces = subsets(5, 3)
    tets = subsets(5, 4)
    V, E, F, T = map(len, (vertices, edges, faces, tets))
    d0 = [sum((1 << i) for i, v in enumerate(vertices) if v <= e)
          for e in edges]
    phi = [sum((1 << i) for i, e in enumerate(edges) if e <= f)
           for f in faces]
    dual = [sum((1 << i) for i, f in enumerate(faces) if f <= t)
            for t in tets]
    assert (V, E, F, T) == (5, 10, 10, 5)
    assert (rank(d0, V), rank(phi, E), rank(dual, F)) == (4, 6, 4)
    assert all(eval_rows(phi, eval_rows(d0, x)) == 0 for x in range(1 << V))
    fan_cycles = [eval_rows(phi, x) for x in range(1 << E)]
    assert all(eval_rows(dual, z) == 0 for z in fan_cycles)
    span = set(fan_cycles)
    dual_cycles = {z for z in range(1 << F) if eval_rows(dual, z) == 0}
    assert len(span) == len(dual_cycles) == (1 << (T + 1)) == 64
    assert span == dual_cycles
    primal_edge_rows = [sum((1 << i) for i, f in enumerate(faces) if e <= f)
                        for e in edges]
    primal_cycles = {s for s in range(1 << F)
                     if all((row & s).bit_count() % 2 == 0
                            for row in primal_edge_rows)}
    assert len(primal_cycles) == 16
    assert all((s & z).bit_count() % 2 == 0
               for s in primal_cycles for z in dual_cycles)
    potential_images = {sum((((b >> i) & 1) ^ ((b >> j) & 1)) << k
                            for k, (i, j) in enumerate(
                              tuple(tuple(q for q, t in enumerate(tets) if f <= t)
                                    for f in faces)))
                        for b in range(1 << T)}
    assert len(potential_images) == 16
    assert potential_images == primal_cycles
    print('FIXTURE := boundary_of_4_simplex')
    print(f'V={V} E={E} F={F} T={T}')
    print('RANK_D0=4 RANK_PHI=6 RANK_DUAL=4')
    print('DUAL_CYCLES=64 FAN_SPAN=64 PRIMAL_FACE_CYCLES=16')
    print('PAIRINGS_CHECKED=1024 POTENTIALS=32')
    print('EXHAUSTIVE_F2_FIXTURE := PASS')


if __name__ == '__main__':
    main()
