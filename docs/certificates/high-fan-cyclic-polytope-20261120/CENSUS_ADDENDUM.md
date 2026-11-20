# C6 high-fan exact two-step census — addendum

Status: **COMPUTATION_PASS (independent bounded enumeration)**.
Lean compilation, axiom audit, and full fail-closed hypothesis check: **NOT RUN**.
Audit base: `0f1b2683edd2d89576c941d2b17b1110a42ef83d`.

## Method

Read the nine tetrahedron supports in
`docs/certificates/high-fan-cyclic-polytope-20261120/VERIFICATION.md`.
Enumerate all ordered central vertex pairs `(v,x)`, all ordered
different left/right tetrahedral supports containing `v,x`,
transverse vertex `y` shared by their link triangles at `v`,
and chord endpoints `(z0,z1)` occurring in the respective
left/right supports, with five distinct vertices. For each such
configuration enumerate *all* represented witness tetrahedra containing
`z0,z1` and omitting `v` or `x`. Require chord-edge incidence
exactly three. Count actual tuples of supports and integer labels,
not proofs and not choices of ordering within `Tet` or `LinkTriangle`.

Next enumerate ordered pairs of records `(A,B)` satisfying BOTH
`(A.z0,A.z1)=(B.v,B.x)` and
`(B.z0,B.z1)=(A.v,A.x)`. This is exact two-step chord closure,
stronger than unordered-edge return.

## Results

| Quantity | Exact count |
| --- | ---: |
| Canonical ordered geometric witness records | **576** |
| Ordered two-step return pairs | **288** |
| Two-step pairs modulo swapping A/B | **144** |
| Ordered two-step pairs with different transverse vertices | **288** |
| Witness records whose chord has incidence 3 | **576** |

The finite algorithm has no statistical sampling and uses only integer
membership, subset tests and enumeration. Reproduction:

```bash
python3 research/certificates/high_fan_c6/check_c6_high_fan.py
python3 research/certificates/high_fan_c6/census_two_step.py
```

The source-level `FanChordTransition` record stores more than these
canonical support tuples. In particular the concrete Lean constructors
and a `ClosedTriangulationCore` proof for the fixture are not included,
so do **not** assert an exact cardinality of
`HighFanState K` based on the 576 records. The result is an exhaustive
census within this explicitly enumerated canonical combinatorial model.

## Mathematical implication and boundary

A two-step high-fan return with different transverse vertices is
compatible with closed simplicial 3-sphere incidence and with every
vertex's tetrahedron-occurrence degree being six. It cannot be excluded
by the existing **same-transverse** two-cycle lemma or by a
no-degree-four assumption alone.

The fixture has an explicit combinatorial 3-to-2 replacement decreasing
`PhiSupport` from 12 to 8. Thus it does **not** challenge a theorem
whose hypotheses include *no strict descent*. It shows precisely
why no-descent or another stronger invariant must be used in a cycle
exclusion proof.

Do not infer termination or global Poincare from finite recurrence or
from the existence of these cycles.

**C6_CENSUS := COMPUTATION_PASS**.
**LEAN_VERIFIED := NOT_RUN**.
**NO_DESCENT := FALSE_FOR_THIS_FIXTURE**.
**GLOBAL_CYCLE_EXCLUSION := OPEN**.
**GLOBAL_POINCARE := OPEN**.
