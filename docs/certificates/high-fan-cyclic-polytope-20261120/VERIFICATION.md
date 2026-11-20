# High-fan two-cycle: six-vertex cyclic 4-polytope boundary

Status: **EXACT FINITE COMPUTATION PASS; LEAN NOT RUN; GLOBAL POINCARE OPEN**.

Audit date: 2026-11-20. Source declarations inspected at repository commit
`0f1b2683edd2d89576c941d2b17b1110a42ef83d`:
`GlobalFanChordTransition.lean`, `GlobalFanChordEdgeProgress.lean`,
`GlobalMove32SourceFaceHighFanAvoidance.lean`,
`GlobalFanReentryModeLinkedStep.lean`,
`GlobalFanReentryModeLinkedSuccessor.lean`,
and `Triangulation.lean`. This is a research fixture, **not** a Lean theorem.

## Exact triangulation

Vertices `0,1,2,3,4,5`; the nine tetrahedral supports are

```text
0123 0125 0134 0145 0235 0345 1234 1245 2345
```

This is the boundary of the cyclic 4-polytope `C(6,4)`:
the facets satisfy Gale evenness; an independent exact integer determinant
test on moment-curve points `(i,i²,i³,i⁴)` gives the same nine facets.
Every one of the 18 triangular faces has exactly two incident tetrahedra,
and each of the six vertices has tetrahedron-occurrence degree 6.
Thus no vertex has degree 4. Because the complex is the convex polytope
boundary, its underlying space is homeomorphic to `S³`.

## Two local fan-chord witness packages

A: central edge `(v,x)=(0,2)`; transverse `y=1`;
chord `(z0,z1)=(3,5)`; ordered adjacent left/right tetrahedra
`0123,0125`; off-old-edge chord witness `0345` (contains 3,5
but omits 2). Their link triangles at 0 are `123` and `125`,
sharing 1 besides star vertex 2. Five distinct vertices:
`[0,2,1,3,5]`.

B: central edge `(v,x)=(3,5)`; transverse `y=4`;
chord `(z0,z1)=(0,2)`; ordered adjacent left/right tetrahedra
`0345,2345`; off-old-edge chord witness `0123` (contains 0,2
but omits 5). Their link triangles at 3 are `045` and `245`,
sharing 4 besides star vertex 5. Five distinct vertices:
`[3,5,4,0,2]`.

The chord incidences `35` and `02` are both exactly 3, so both
`FanChordTransition.incidence` witnesses are in its exact-three branch.
All prescribed finite, membership, shared-vertex, distinctness,
left/right-match and escape fields have been checked combinatorially.
The whole Lean structures have **not** been elaborated or kernel-checked.

Consequently, the local transition geometry admits a two-step return
`02 → 35 → 02` with different transverse vertices `1 ≠ 4`.
This refutes the *candidate inference* that no-degree-four plus the
local fan-chord witness conditions excludes every two-cycle. It does
**not** refute the existing same-transverse two-cycle theorem.

## Strict-descent alternative is present

Edge `02` has star `0123,0125,0235`.
The combinatorial `3→2` replacement removes those three tetrahedra
and inserts `0135,1235`. The resulting eight-tetrahedron complex
again has two incident tetrahedra at each triangular face.

As defined in `Triangulation.lean`, `vertexDegree` counts vertex
occurrences in tetrahedra and `PhiSupport` sums
`|vertexDegree(v)-4|` over distinct supported vertices. Before:
six vertices of degree 6, so `PhiSupport = 12`.
After: vertices 0,2 have degree 4 and the other four retain degree 6,
so `PhiSupport = 8`. Therefore `ΔPhiSupport = -4`.
This is an exact *combinatorial* calculation. A Lean
`Move32Site` legal-realization/topological-homeomorphism certificate
for this particular fixture was **NOT RUN**. Hence this example does
not satisfy the hypothesized absence of strict descent.

## Reproducible exact check (Python standard library)

Run as a self-contained script. No dependencies, downloads, writes,
or repository modifications are required.

```python
from itertools import combinations
from collections import Counter

V = set(range(6))
facets = {
    frozenset(map(int, t)) for t in (
        "0123", "0125", "0134", "0145", "0235",
        "0345", "1234", "1245", "2345"
    )
}
def gale(f):
    a, b = sorted(V - set(f))
    return sum(a < x < b for x in f) % 2 == 0

assert facets == {
    frozenset(t) for t in combinations(sorted(V), 4) if gale(t)
}
def face_counts(T):
    return Counter(frozenset(s) for t in T for s in combinations(sorted(t), 3))
def degree(T):
    return {v: sum(v in t for t in T) for v in V}
def phi(T):
    return sum(abs(k - 4) for k in degree(T).values())
assert len(facets) == 9
assert len(face_counts(facets)) == 18
assert set(face_counts(facets).values()) == {2}
assert set(degree(facets).values()) == {6}
def edge_tets(edge):
    return {t for t in facets if set(edge) <= t}
assert len(edge_tets((0, 2))) == 3
assert len(edge_tets((3, 5))) == 3
def transition(v, x, y, z0, z1, left, right, witness):
    assert len({v, x, y, z0, z1}) == 5
    assert left in facets and right in facets and witness in facets
    assert {v, x, y, z0} <= left
    assert {v, x, y, z1} <= right
    assert {z0, z1} <= witness
    assert v not in witness or x not in witness
    assert len(edge_tets((z0, z1))) == 3
    assert len({v, x, y}) == 3
    # Link triangles at v are the other vertices in these tetrahedra.
    sigma, rho = left - {v}, right - {v}
    assert sigma != rho and {x, y} <= sigma & rho

transition(0, 2, 1, 3, 5,
           frozenset((0, 1, 2, 3)),
           frozenset((0, 1, 2, 5)),
           frozenset((0, 3, 4, 5)))
transition(3, 5, 4, 0, 2,
           frozenset((0, 3, 4, 5)),
           frozenset((2, 3, 4, 5)),
           frozenset((0, 1, 2, 3)))
removed = edge_tets((0, 2))
assert removed == {
    frozenset(map(int, t)) for t in ("0123", "0125", "0235")
}
added = {frozenset(map(int, t)) for t in ("0135", "1235")}
assert not added & facets
result = (facets - removed) | added
assert len(result) == 8
assert set(face_counts(result).values()) == {2}
assert phi(facets) == 12 and phi(result) == 8
print("C6_GALE_FACETS := PASS")
print("CLOSED_FACE_INCIDENCE := PASS")
print("LOCAL_TWO_STEP_PATTERN := PASS")
print("COMBINATORIAL_DESCENT := PASS")
print("PHI_BEFORE := 12")
print("PHI_AFTER := 8")
print("LEAN_CERTIFICATE := NOT_RUN")
print("GLOBAL_POINCARE := OPEN")
```

## Formalization and research boundary

1. `Finite (HighFanState K)` is a mathematically justified but uncompiled
   finite-support/proof-irrelevance target.
2. Under no legal Move23/no strict descent, fan-only continuation with
   edge change and without `hNoHigh` has a paper-level proof from
   `FanChordTransition.continue` and source-face high-fan reinjection.
   Its complete Lean declaration is **NOT VERIFIED**.
3. Full-state recurrence would follow by finite pigeonhole once (1) and
   (2) are Lean verified. Complete-state recurrence alone cannot exclude
   cycles: the fixture here demonstrates real geometric two-step
   transitions, though it has a descent.
4. Remaining substantive obligation: prove that every recurrent
   high-fan/reinjection trajectory under the full no-move/no-descent
   hypotheses is impossible, using a genuinely global geometric invariant.
   Do not infer this from recurrence, unchanged `PhiSupport`, or
   same-transverse two-cycle exclusion alone.

**CERTIFICATE_STATUS := EXACT_FINITE_CHECK**.
**HIGH_FAN_LEAN_INTEGRATION := NOT_RUN**.
**CYCLIC_RIGIDITY := OPEN**.
**GLOBAL_POINCARE := OPEN**.

Git hygiene: documentation-only checkpoint on a dedicated research branch;
no local Mac changes, no merge, no promoted formal theorem.
