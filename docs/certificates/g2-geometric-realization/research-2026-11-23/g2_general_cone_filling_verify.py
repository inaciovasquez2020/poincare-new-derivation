#!/usr/bin/env python3
"""Independent exact finite checks of the chain-level cone-of-graph filler.

For simple graph G on vertices 0..n-1, oriented graph edges u<v,
cone vertex c, triangle s_(u,v)=[c,u,v]:
  d2(s_e) = (outer edge e, radial at u minus radial at v).
For z=(outer, radial), z is a cycle iff radial=-d_G outer.
The inverse of d2 restricted to cycles is projection onto outer edges.
All exact arithmetic. No dependencies, repo writes, or network.
"""
from itertools import combinations, product
from collections import Counter
import random
import time

START = time.monotonic()
RNG = random.Random(20261123)
MAX_SECONDS = 25
COUNTS = Counter()


def incidence(n, edges, outer):
    """Independent oriented base-graph boundary of outer edge chain."""
    d = [0]*n
    for (u, v), a in zip(edges, outer):
        d[u] -= a
        d[v] += a
    return d


def cone_boundary2(n, edges, triangles):
    """The signed simplicial boundary of [c,u,v], u<v."""
    rad = [0]*n
    outer = [0]*len(edges)
    for i, ((u, v), a) in enumerate(zip(edges, triangles)):
        outer[i] += a
        rad[u] += a
        rad[v] -= a
    return outer, rad


def cone_boundary1(n, edges, outer, radial):
    """Vertex coefficients, independently derived from edge orientations."""
    d = incidence(n, edges, outer)
    for i, a in enumerate(radial):
        d[i] += a
    return [-sum(radial), *d]


def check(n, edges, outer, radial, mod=None):
    bd = cone_boundary1(n, edges, outer, radial)
    iscycle = all((x % mod == 0 if mod else x == 0) for x in bd)
    dg = incidence(n, edges, outer)
    formula = all(((radial[i]+dg[i]) % mod == 0 if mod else radial[i]+dg[i] == 0) for i in range(n))
    assert iscycle == formula, (n, edges, outer, radial, mod)
    if iscycle:
        o2, r2 = cone_boundary2(n, edges, outer)
        if mod:
            assert all((a-b) % mod == 0 for a,b in zip(outer,o2))
            assert all((a-b) % mod == 0 for a,b in zip(radial,r2))
        else:
            assert outer == o2 and radial == r2
        COUNTS['cycle_inverse_checks'] += 1
    COUNTS['chains_tested'] += 1


# Exhaustively enumerate every simple graph and every F2 1-chain, n <= 4.
for n in range(0,5):
    all_edges = list(combinations(range(n),2))
    for mask in range(1 << len(all_edges)):
        edges = tuple(e for i,e in enumerate(all_edges) if mask & (1 << i))
        m = len(edges)
        COUNTS['graph_cases'] += 1
        expected_cycles = 1 << m
        cycles_seen = 0
        # Each graph contributes 2^(m+n) chains, bounded at n<=4.
        for state in range(1 << (m+n)):
            outer = [(state >> i) & 1 for i in range(m)]
            radial = [(state >> (m+i)) & 1 for i in range(n)]
            was_cycle = all(x % 2 == 0 for x in cone_boundary1(n, edges, outer, radial))
            check(n, edges, outer, radial, mod=2)
            cycles_seen += int(was_cycle)
        assert cycles_seen == expected_cycles, (n, edges, cycles_seen, expected_cycles)
        COUNTS['cycle_count_checks'] += 1
        if time.monotonic() - START > MAX_SECONDS:
            raise SystemExit('RESULT := INCOMPLETE_TIME_GUARD')

# Adversarial exact integer tests, noncyclic, disconnected and sparse graphs.
for n in (3,4,5,6,8,12,20):
    all_edges = list(combinations(range(n),2))
    for p in (0.0,0.1,0.3,0.5,0.9,1.0):
        edges = tuple(e for e in all_edges if RNG.random() < p)
        for trial in range(200):
            a = [RNG.randint(-100,100) for _ in edges]
            outer, radial = cone_boundary2(n, edges, a)
            assert cone_boundary1(n, edges, outer, radial) == [0]*(n+1)
            check(n, edges, outer, radial)
            # Perturb one radial coefficient to force a noncycle.
            if n:
                bad = radial.copy()
                bad[trial % n] += RNG.choice((-7,-1,1,13))
                assert any(cone_boundary1(n,edges,outer,bad))
                check(n, edges, outer, bad)
            COUNTS['integer_pair_trials'] += 1
            if time.monotonic() - START > MAX_SECONDS:
                raise SystemExit('RESULT := INCOMPLETE_TIME_GUARD')

print('RESULT := COMPUTATION_PASS')
print('GRAPH_CASES :=', COUNTS['graph_cases'])
print('F2_CHAIN_EXHAUSTIVE_CHECKS :=', COUNTS['chains_tested']-2*COUNTS['integer_pair_trials'])
print('F2_CYCLE_COUNT_CHECKS :=', COUNTS['cycle_count_checks'])
print('Z_INTEGER_PAIRS :=', COUNTS['integer_pair_trials'])
print('TOTAL_CHAIN_CHECKS :=', COUNTS['chains_tested'])
print('CYCLE_INVERSE_CHECKS :=', COUNTS['cycle_inverse_checks'])
print('MAX_N := 20')
print('RNG_SEED := 20261123')
print('MAX_SECONDS :=', MAX_SECONDS)
print('ELAPSED_SECONDS :=', round(time.monotonic()-START,3))
print('UNRESTRICTED_PROOF := PAPER_ALGEBRA')
print('LEAN := NOT_RUN')
print('REPOSITORY_MODIFIED := FALSE')
