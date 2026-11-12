"""Replay finite Pachner descent on the Dougherty–Faber–Murphy 3-sphere.

The published 16-vertex sphere is described in DOI 10.1007/s00454-004-1097-3.
The cyclic facet presentation appears in Bagchi and Datta, On k-stellated
and k-stacked spheres. This is a computational fixture for that sphere,
with no Lean or universal descent claim.

Run from the repository root:
    python3 scripts/tests/dfm_stabilized_descent_certificate.py
"""

from collections import Counter, defaultdict, deque
from itertools import combinations


FACET_ORBITS = (
    (0, 1, 4, 6), (0, 1, 4, 9), (0, 1, 6, 14), (0, 1, 8, 9),
    (0, 1, 8, 10), (0, 1, 10, 14), (0, 2, 9, 13),
)

# Each pair specifies the removed simplex and the inserted simplex.
PREFIX = (
    ((1, 7, 8, 15), (16,)),
    ((1, 7, 15), (2, 16)),
    ((1, 7, 8), (5, 16)),
    ((1, 7), (2, 5, 16)),
    ((3, 4, 9), (1, 7)),
    ((4, 9), (0, 1, 7)),
    ((0, 4), (1, 6, 7)),
    ((3, 9), (1, 7, 10)),
    ((0, 6), (1, 7, 14)),
    ((0, 2, 8), (3, 9)),
    ((2, 8), (3, 6, 9)),
)
SWEEP = (
    ((1, 15, 16), (2, 8)),
    ((15, 16), (2, 7, 8)),
    ((7, 16), (2, 5, 8)),
    ((16,), (1, 2, 5, 8)),
)
EXPECTED_DEFECT = (
    352, 360, 364, 368, 364, 368, 364, 360,
    356, 352, 356, 352, 356, 352, 348, 340,
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def incident(tetrahedra, simplex):
    return {tet for tet in tetrahedra if simplex <= tet}


def link(tetrahedra, simplex):
    return {
        frozenset(face)
        for tet in incident(tetrahedra, simplex)
        for size in range(len(tet - simplex) + 1)
        for face in combinations(tet - simplex, size)
    }


def represented_faces(tetrahedra, size):
    return Counter(
        frozenset(face)
        for tet in tetrahedra
        for face in combinations(tet, size)
    )


def defect(tetrahedra):
    degrees = Counter(vertex for tet in tetrahedra for vertex in tet)
    return sum(abs(degree - 4) for degree in degrees.values())


def check_closed_core(tetrahedra):
    require(all(len(tet) == 4 for tet in tetrahedra), "degenerate tetrahedron")
    require(set(represented_faces(tetrahedra, 3).values()) == {2},
            "triangle incidence differs from two")


def flip(tetrahedra, removed, inserted):
    a, b = frozenset(removed), frozenset(inserted)
    require(a and b and not a & b and len(a | b) == 5, "invalid move labels")
    old = incident(tetrahedra, a)
    require(old == {a | (b - {v}) for v in b}, "incorrect source star")
    require(not incident(tetrahedra, b), "replacement simplex is already present")
    result = tetrahedra - old | {b | (a - {v}) for v in a}
    check_closed_core(result)
    return result


def extra_common_link(tetrahedra, u, v):
    common = link(tetrahedra, {u}) & link(tetrahedra, {v})
    return common - link(tetrahedra, {u, v})


def legal_moves(tets):
    # A new vertex has no incidence data, so one fresh label suffices.
    vertices = {v for tet in tets for v in tet}
    fresh = next(i for i in range(len(vertices) + 1) if i not in vertices)
    yield from ((tet, frozenset({fresh})) for tet in tets)
    for size in (1, 2, 3):
        stars = defaultdict(set)
        for tet in tets:
            for face in combinations(tet, size):
                stars[frozenset(face)].add(tet)
        for a, star in stars.items():
            if len(star) != 5 - size:
                continue
            b = frozenset.union(*star) - a
            if len(b) != 5 - size:
                continue
            if star == {a | (b - {v}) for v in b} and not incident(tets, b):
                yield a, b

def check_lower_bound(tetrahedra):
    start = frozenset(tetrahedra)
    initial_defect = defect(start)
    seen = {start}
    pending = deque([start])
    while pending:
        state = pending.popleft()
        for a, b in legal_moves(state):
            replacement = {b | (a - {v}) for v in a}
            candidate = (state - incident(state, a)) | replacement
            candidate_defect = defect(candidate)
            if candidate_defect > 364 or candidate in seen:
                continue
            require(candidate_defect >= initial_defect, "descent at or below 364")
            check_closed_core(candidate)
            seen.add(candidate)
            require(len(seen) <= 313, "state limit exceeded before closure")
            pending.append(candidate)

    histogram = Counter(map(defect, seen))
    require(histogram == {352: 1, 360: 104, 364: 208},
            "unexpected sublevel component")
    print("SUBLEVEL_COMPONENT := 313")


def main():
    tetrahedra = {
        frozenset((v + shift) % 16 for v in facet)
        for facet in FACET_ORBITS
        for shift in range(16)
    }
    check_closed_core(tetrahedra)
    edges = represented_faces(tetrahedra, 2)
    require(len(tetrahedra) == 104 and len(edges) == 120, "wrong fixture size")
    require(min(edges.values()) >= 4, "initial degree-three edge")
    require(min(Counter(v for tet in tetrahedra for v in tet).values()) > 4,
            "initial degree-four vertex")
    require(all(extra_common_link(tetrahedra, *edge) for edge in edges),
            "initial edge satisfies the link condition")

    check_lower_bound(tetrahedra)
    profile = [defect(tetrahedra)]
    for step, (a, b) in enumerate(PREFIX, 1):
        tetrahedra = flip(tetrahedra, a, b)
        profile.append(defect(tetrahedra))
        if step == 10:
            require(extra_common_link(tetrahedra, 2, 16) == {frozenset({8})},
                    "wrong sole obstruction before move 11")
            require(extra_common_link(tetrahedra, 8, 16) == {frozenset({2})},
                    "wrong reciprocal obstruction before move 11")

    require(not extra_common_link(tetrahedra, 2, 16), "edge 2–16 still blocked")
    require(not extra_common_link(tetrahedra, 8, 16), "edge 8–16 still blocked")
    require(len(incident(tetrahedra, {2, 16})) == 4, "wrong contraction degree")
    contracted = {
        (tet - {16}) | {2} if 16 in tet else tet
        for tet in tetrahedra
        if not {2, 16} <= tet
    }
    for a, b in SWEEP:
        tetrahedra = flip(tetrahedra, a, b)
        profile.append(defect(tetrahedra))

    require(tetrahedra == contracted, "sweep differs from direct contraction")
    require(tuple(profile) == EXPECTED_DEFECT, "unexpected defect profile")
    vertices = {v for tet in tetrahedra for v in tet}
    require(len(tetrahedra) == 101 and len(vertices) == 16,
            "unexpected final counts")
    print("DEFECT_PROFILE := " + " -> ".join(map(str, profile)))
    print("DFM_STABILIZED_DESCENT_CERTIFICATE := PASS")


if __name__ == "__main__":
    main()
