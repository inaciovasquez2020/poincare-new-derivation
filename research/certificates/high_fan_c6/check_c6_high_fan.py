"""Exact C(6,4) high-fan two-step and combinatorial descent audit.

Standard library only. No Lean theorem or topological descent certificate claimed.
"""
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
