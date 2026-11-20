"""Exhaustive local high-fan witness census on the boundary C(6,4).

Enumerates oriented central edges, ordered left/right tetrahedra,
transverse vertices, ordered chord endpoints and off-edge witnesses.
This is a finite combinatorial certificate, NOT a Lean compilation or
a fail-closed global Poincare counterexample.
"""
from itertools import permutations
from collections import Counter

VERTICES = tuple(range(6))
TETS = tuple(sorted((
    frozenset(map(int, t)) for t in
    ("0123", "0125", "0134", "0145", "0235",
     "0345", "1234", "1245", "2345")
), key=lambda s: tuple(sorted(s))))
def incidence(edge):
    return sum(set(edge) <= t for t in TETS)

states = set()
for v, x in permutations(VERTICES, 2):
    for left, right in permutations(TETS, 2):
        if not ({v, x} <= left and {v, x} <= right):
            continue
        sigma = left - {v}
        rho = right - {v}
        # Link-star adjacency: triangles distinct, sharing x and
        # a third vertex y other than x.
        if sigma == rho:
            continue
        for y in (sigma & rho) - {x}:
            for z0 in left - {v, x, y}:
                for z1 in right - {v, x, y}:
                    if len({v, x, y, z0, z1}) != 5:
                        continue
                    if not ({x, y} <= sigma & rho):
                        continue
                    if incidence((z0, z1)) != 3:
                        continue
                    for witness in TETS:
                        if {z0, z1} <= witness and (
                            v not in witness or x not in witness
                        ):
                            states.add((
                                v, x, y, z0, z1,
                                tuple(sorted(left)),
                                tuple(sorted(right)),
                                tuple(sorted(witness))
                            ))

# All possible *two-step* returns with exact ordered endpoint
# agreement, not merely matching unordered edge keys.
pairs = {
    (a, b)
    for a in states
    for b in states
    if (a[3], a[4]) == (b[0], b[1])
    and (b[3], b[4]) == (a[0], a[1])
}
assert len(states) == 576, len(states)
assert len(pairs) == 288, len(pairs)
assert all(a[2] != b[2] for a, b in pairs)
assert len({tuple(sorted((a, b))) for a, b in pairs}) == 144
assert all(incidence((s[3], s[4])) == 3 for s in states)
# Every pair uses the exact same central edge as the previous
# chord, and the transverse vertices differ.
print("C6_ORDERED_WITNESS_STATES := 576")
print("C6_ORDERED_TWO_STEP_RETURN_PAIRS := 288")
print("C6_UNORDERED_TWO_STEP_RETURN_PAIRS := 144")
print("C6_DIFFERENT_TRANSVERSE_TWO_STEP_PAIRS := 288")
print("C6_CHORD_INCIDENCE_THREE := PASS")
print("C6_EXHAUSTIVE_LOCAL_CENSUS := COMPUTATION_PASS")
print("CLOSED_CORE_LEAN_VERIFICATION := NOT_RUN")
print("NO_DESCENT_HYPOTHESIS := FALSE_FOR_THIS_FIXTURE")
print("GLOBAL_POINCARE := OPEN")
