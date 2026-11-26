#!/usr/bin/env python3
"""Finite fixed-triangulation FanChordTransition projection check.

Source: Poincare/Move2332CrossPolytopeEscape.lean,
crossPolytopeEscapeAfter32₁_tets, main 62ac9107fe10c163a33902fb1bded9fff1d8cf4d.
This checker does NOT verify global fan/reentry mode continuation, a Lean proof,
or normalized descent. Graph vertices forget orientation, sigma/rho, and carriers.
A cycle of full FanChordTransitions would project to a graph cycle, so a
cycle-free projected graph excludes those cycles on this ONE fixed fixture.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import re
from pathlib import Path
from collections import Counter, defaultdict

# Exactly the 16 tetrahedra of crossPolytopeEscapeAfter32₁_tets, in Lean order.
TETS = (
    (1, 6, 7, 2), (1, 6, 7, 4), (0, 2, 6, 7), (0, 4, 6, 7),
    (0, 2, 5, 6), (0, 2, 5, 7), (0, 3, 4, 6), (0, 3, 4, 7),
    (0, 3, 5, 6), (0, 3, 5, 7), (1, 2, 5, 6), (1, 2, 5, 7),
    (1, 3, 4, 6), (1, 3, 4, 7), (1, 3, 5, 6), (1, 3, 5, 7),
)


def digest(obj: object) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def check() -> dict:
    source = (Path(__file__).resolve().parents[1] / "lean" / "Poincare" /
              "Move2332CrossPolytopeEscape.lean").read_text(encoding="utf-8")
    stmt = source.split("theorem crossPolytopeEscapeAfter32₁_tets :", 1)[1].split(":= by", 1)[0]
    matches = re.findall(r"⟨(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩", stmt)
    assert tuple(tuple(map(int, t)) for t in matches) == TETS, "fixture no longer matches the verified Lean theorem"
    tets = tuple(frozenset(t) for t in TETS)
    assert len(tets) == len(set(tets)) == 16
    assert all(len(t) == 4 for t in tets)
    assert set().union(*tets) == set(range(8))
    faces = Counter(frozenset(f) for t in tets for f in itertools.combinations(t, 3))
    assert len(faces) == 32 and set(faces.values()) == {2}

    edge_tets: dict[tuple[int, int], list[int]] = defaultdict(list)
    for index, tet in enumerate(tets):
        for e in itertools.combinations(sorted(tet), 2):
            edge_tets[e].append(index)

    def canon(a: int, b: int) -> tuple[int, int]:
        return (min(a, b), max(a, b))

    def contains(t: frozenset[int], verts: tuple[int, ...]) -> bool:
        return set(verts) <= t

    # The same ordered target-tetrahedron membership criterion used by
    # crossPolytope_secondMove_bounded_enumeration, with d=0 and e=4.
    six = [
        [a, b, c]
        for a, b, c in itertools.product(range(8), repeat=3)
        if all(any(t == frozenset(target) and len(set(target)) == 4 for t in tets)
               for target in ((0, 4, a, b), (0, 4, a, c), (0, 4, b, c)))
    ]
    expected_six = [[3, 6, 7], [3, 7, 6], [6, 3, 7],
                    [6, 7, 3], [7, 3, 6], [7, 6, 3]]
    assert six == expected_six
    assert {frozenset(s) for s in six} == {frozenset((3, 6, 7))}
    assert len(edge_tets[(0, 4)]) == 3
    assert not any(contains(t, (3, 6, 7)) for t in tets)

    transitions = []
    for (v, x), local in sorted(edge_tets.items()):
        for i, j in itertools.combinations(local, 2):
            left, right = tets[i], tets[j]
            shared = left & right
            # Source link-star adjacency: common face {v,x,y}, distinct tets.
            if len(shared) != 3 or not {v, x} <= shared:
                continue
            y, = shared - {v, x}
            z0, = left - shared
            z1, = right - shared
            assert len({v, x, y, z0, z1}) == 5
            assert faces[frozenset((v, x, y))] == 2
            chord = canon(z0, z1)
            # FanChordTransition.witness_mem, z0_mem, z1_mem,
            # and escapes_old_edge. Exclude legal NewEdgeAbsent sites.
            witnesses = [k for k, t in enumerate(tets)
                         if {z0, z1} <= t and (v not in t or x not in t)]
            if not witnesses:
                continue
            degree = len(edge_tets[chord])
            assert degree == 3 or degree >= 4
            transitions.append({
                "old": [v, x], "source_tets": [i, j], "transverse": y,
                "chord": list(chord), "chord_incidence": degree,
                "off_old_edge_witness_tets": witnesses,
            })

    # Edges are *unordered* central-edge keys; this projects away all the
    # FanChordTransition proof fields, including both orientations.
    arcs = sorted({(tuple(e["old"]), tuple(e["chord"])) for e in transitions})
    sources = {s for s, _ in arcs}
    targets = {d for _, d in arcs}
    assert len(edge_tets) == 24
    assert len(transitions) == 42
    assert len(arcs) == 31
    assert len(sources) == 19
    assert len(targets) == 5
    assert sources.isdisjoint(targets)  # No two consecutive transitions.
    assert targets == {(3, 6), (3, 7), (5, 6), (5, 7), (6, 7)}
    assert all(e["chord_incidence"] >= 4 for e in transitions)
    high = [e for e in transitions if len(edge_tets[tuple(e["old"])]) >= 4]
    assert len(high) == 30 and len({tuple(e["old"]) for e in high}) == 15
    assert all(len(edge_tets[t]) >= 4 for t in targets)
    return {
        "scope": "crossPolytopeEscapeAfter32₁ (16 tetrahedra), fixed K, unordered-edge projection",
        "source_commit": "62ac9107fe10c163a33902fb1bded9fff1d8cf4d",
        "fixture_sha256": digest(TETS),
        "six_ordered_move32_candidates": six,
        "six_distinct_geometric_move32_sites": 1,
        "represented_edges": len(edge_tets),
        "high_edges": sum(len(t) >= 4 for t in edge_tets.values()),
        "transition_witnessed_adjacent_pairs": len(transitions),
        "transition_unordered_edge_arcs": len(arcs),
        "transition_source_edge_count": len(sources),
        "terminal_chord_edges": [list(t) for t in sorted(targets)],
        "high_source_transition_pairs": len(high),
        "source_target_edge_intersection": len(sources & targets),
        "directed_cycles": 0,
        "max_projected_transition_path_length": 1,
        "arcs_sha256": digest([[list(s), list(d)] for s, d in arcs]),
        "transitions_sha256": digest(transitions),
    }


if __name__ == "__main__":
    print(json.dumps(check(), sort_keys=True, indent=2))
