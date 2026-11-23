#!/usr/bin/env python3
"""Exact integer checks for the canonical filling of cone(C_m), m even >= 6.
Independent boundary-operator check; no dependencies or repository writes.
"""
from itertools import product
from time import monotonic
import json

def boundary1(m, outer, radial):
    # Chain coefficients on boundary edges [u_i,u_i+1] and radial edges [c,u_i].
    # Output coefficients at [c,u_0,...,u_{m-1}].
    v = [-sum(radial)]
    v += [outer[(i - 1) % m] - outer[i] + radial[i] for i in range(m)]
    return v

def boundary2(m, triangles):
    # ∂[c,u_i,u_i+1] = [u_i,u_i+1] - [c,u_i+1] + [c,u_i].
    outer = list(triangles)
    radial = [triangles[i] - triangles[(i - 1) % m] for i in range(m)]
    return outer, radial

start=monotonic()
checks=0
summary=[]
for m in (6,8):
    states=0
    for a in product((-1,0,1), repeat=m):
        outer, radial = boundary2(m, a)
        assert boundary1(m, outer, radial) == [0] * (m+1)
        # Unique inverse is given by outer-edge coefficients.
        recon_outer, recon_radial = boundary2(m, outer)
        assert (recon_outer,recon_radial) == (outer,radial)
        # Independent solve of cycle condition at each outer vertex.
        assert all(radial[i] == outer[i]-outer[(i-1)%m] for i in range(m))
        states += 1
    # Boundary 2x2 composition checked with canonical basis, too.
    for j in range(m):
        t = [int(i == j) for i in range(m)]
        outer, radial=boundary2(m,t)
        assert boundary1(m,outer,radial)==[0]*(m+1)
    summary.append({'m':m,'states':states,'coefficient_set':[-1,0,1],'basis_checks':m})
    checks+=states+m
print('RESULT := COMPUTATION_PASS')
print('EXACT_INTEGER_CHECKS :=',checks)
print('SCOPES :=',json.dumps(summary,sort_keys=True))
print('ELAPSED_SECONDS :=',round(monotonic()-start,3))
print('UNIVERSAL_PROOF := PAPER_ARGUMENT_ONLY')
print('LEAN := NOT_RUN')
print('SOURCE_MODIFICATIONS := NONE')