#!/usr/bin/env python3
"""Exact rational regression for the dyadic concatenation seam, not a Lean proof."""
from fractions import Fraction as F

def evaluate(vertices, q):
    n = len(vertices) - 1
    if n == 1:
        return (1-q)*vertices[0] + q*vertices[1]
    if q <= F(1, 2):
        return evaluate(vertices[:-1], 2*q)
    t = 2*q-1
    return (1-t)*vertices[-2] + t*vertices[-1]

checks = walks = 0
for m in range(1, 65):
    for vs in ([F(k) for k in range(m)]+[F(0)],
               [F((-1)**k*(k%7)) for k in range(m)]+[F(0)]):
        s = [F(0)] + [F(1, 2**(m-k)) for k in range(1, m+1)]
        assert s[0] == 0 and s[-1] == 1
        assert all(a < b for a, b in zip(s, s[1:]))
        for k in range(m):
            for t in (F(0), F(1,4), F(1,2), F(3,4), F(1)):
                q = s[k] + t*(s[k+1]-s[k])
                assert evaluate(vs,q) == (1-t)*vs[k]+t*vs[k+1], (m,k,t,q)
                checks += 1
        walks += 1
print('EXACT_RATIONAL_SEAM_TEST := COMPUTATION_PASS')
print('WALK_LENGTHS := 1..64')
print('WALKS :=', walks)
print('POINT_CHECKS :=', checks)
print('LEAN_COMPILATION := NOT_RUN')
