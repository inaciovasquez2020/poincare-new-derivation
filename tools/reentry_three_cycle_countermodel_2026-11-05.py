"""Reproducible finite witness: witnessed-reentry 3-cycle in a closed-core
pseudomanifold whose connected vertex links need not be 2-spheres.
This is NOT a Poincare counterexample or a model of a closed 3-manifold.
Python 3; standard library only. No repository source changes.
"""
from collections import Counter, defaultdict
from itertools import combinations

TETRAHEDRA = [
    (0,1,4,6), (0,1,4,7), (0,1,6,7),
    (0,2,3,6), (0,2,3,8), (0,2,5,6),
    (0,2,5,7), (0,2,7,8), (0,3,4,7),
    (0,3,4,8), (0,3,6,7), (0,4,6,8),
    (0,5,6,8), (0,5,7,8), (1,2,4,6),
    (1,2,4,8), (1,2,6,7), (1,2,7,8),
    (1,4,7,8), (2,3,6,8), (2,4,5,7),
    (2,4,5,8), (2,4,6,7), (2,5,6,8),
    (3,4,6,7), (3,4,6,8), (4,5,7,8),
]

# Sites: (source-face a,b,c; shared-edge d,e)
SITES = [
    ((4,6,7), (0,1)),
    ((0,6,8), (2,3)),
    ((2,7,8), (4,5)),
]


def connected(nodes, relation):
    if not nodes:
        return True
    remaining = set(nodes)
    stack = [next(iter(remaining))]
    remaining.remove(stack[0])
    while stack:
        x = stack.pop()
        for y in tuple(remaining):
            if relation(x, y):
                remaining.remove(y)
                stack.append(y)
    return not remaining


def main():
    K = set(TETRAHEDRA)
    assert len(K) == 27 and all(len(t) == 4 and len(set(t)) == 4 for t in K)
    faces = defaultdict(list)
    edges = defaultdict(list)
    vertices = defaultdict(list)
    for t in K:
        for f in combinations(t,3):
            faces[f].append(t)
        for e in combinations(t,2):
            edges[e].append(t)
        for v in t:
            vertices[v].append(t)
    assert sorted(vertices) == list(range(9))
    assert len(edges) == 33 and len(faces) == 54
    assert all(len(incident) == 2 for incident in faces.values())
    print('CLOSED_TRIANGULATION_CORE := PASS')
    assert connected(K, lambda a,b: bool(set(a) & set(b)))
    print('TETRAHEDRON_VERTEX_OVERLAP_CONNECTED := PASS')
    assert all(len(ts) != 4 for ts in vertices.values())
    print('NO_VERTEX_DEGREE_FOUR := PASS')

    link_chi = {}
    for v in vertices:
        triangles = {tuple(x for x in t if x != v) for t in vertices[v]}
        link_edges = {e for tr in triangles for e in combinations(tr,2)}
        link_vertices = {x for tr in triangles for x in tr}
        edge_counts = Counter(e for tr in triangles for e in combinations(tr,2))
        assert all(count == 2 for count in edge_counts.values())
        assert connected(triangles, lambda a,b: len(set(a) & set(b)) >= 2)
        link_chi[v] = len(link_vertices) - len(link_edges) + len(triangles)
    print('VERTEX_LINK_TRIANGLE_ADJACENCY_CONNECTED := PASS')
    assert Counter(link_chi.values()) == Counter({1:6, 2:3})
    print('VERTEX_LINK_EULER_CHARACTERISTICS :=', dict(sorted(link_chi.items())))
    print('ALL_VERTEX_LINKS_TWO_SPHERES := FAIL')

    for i, (source, edge) in enumerate(SITES):
        next_edge = SITES[(i+1)%3][1]
        target = {tuple(sorted((*edge, *pair))) for pair in combinations(source,2)}
        across_face = {tuple(sorted((*source, v))) for v in next_edge}
        assert len(target) == 3 and target <= K
        assert len(edges[edge]) == 3
        assert len(faces[source]) == 2
        assert across_face == set(faces[source])
        assert edge != next_edge and set(edge).isdisjoint(next_edge)
        assert set(next_edge).isdisjoint((*source,*edge))
        assert len(edges[next_edge]) == 3
        print('WITNESSED_REENTRY_STEP_%d := PASS' % i)
    print('THREE_STEP_CHANGING_CARRIER_CYCLE := PASS')

    required = set()

    for i, (face, edge) in enumerate(SITES):
        next_edge = SITES[(i + 1) % len(SITES)][1]

        required.update(
            tuple(sorted((*edge, *pair)))
            for pair in combinations(face, 2)
        )

        required.update(
            tuple(sorted((*face, vertex)))
            for vertex in next_edge
        )

    assert len(required) == 15
    assert required <= K

    print("PLANARITY_WITNESS_TETRAHEDRA := 15")

    for vertex in (6, 7, 8):
        triangles = {
            tuple(x for x in tetrahedron if x != vertex)
            for tetrahedron in required
            if vertex in tetrahedron
        }

        link_vertices = {
            x for triangle in triangles for x in triangle
        }

        link_edges = {
            pair
            for triangle in triangles
            for pair in combinations(triangle, 2)
        }

        V = len(link_vertices)
        E = len(link_edges)

        assert V == 8
        assert E == 19
        assert E > 3 * V - 6

        print(f"PLANARITY_VERTEX_{vertex} := PASS")
        print(f"LINK_GRAPH_VERTICES := {V}")
        print(f"LINK_GRAPH_EDGES := {E}")
        print(f"PLANAR_EDGE_BOUND := {3 * V - 6}")


    k5_witnesses = {
        6: (
            (0, 2, 3, 4, 7),
            (
                (0, 1, 4, 6),
                (0, 1, 6, 7),
                (0, 2, 3, 6),
                (2, 4, 6, 7),
                (3, 4, 6, 7),
            ),
        ),
        7: (
            (0, 1, 2, 4, 6),
            (
                (0, 1, 4, 7),
                (0, 1, 6, 7),
                (0, 2, 7, 8),
                (1, 2, 7, 8),
                (2, 4, 6, 7),
            ),
        ),
        8: (
            (0, 2, 4, 5, 6),
            (
                (0, 2, 3, 8),
                (0, 4, 6, 8),
                (0, 5, 6, 8),
                (2, 3, 6, 8),
                (2, 4, 5, 8),
            ),
        ),
    }

    def link_contains_k5(tetrahedra, vertex):
        triangles = {
            tuple(x for x in t if x != vertex)
            for t in tetrahedra if vertex in t
        }
        edges = {
            edge
            for triangle in triangles
            for edge in combinations(triangle, 2)
        }
        vertices = sorted({
            x for triangle in triangles for x in triangle
        })
        return any(
            all(edge in edges for edge in combinations(five, 2))
            for five in combinations(vertices, 5)
        )

    for vertex, (clique, witness) in k5_witnesses.items():
        assert len(witness) == 5
        assert set(witness) <= required

        triangles = {
            tuple(x for x in t if x != vertex)
            for t in witness if vertex in t
        }
        edges = {
            edge
            for triangle in triangles
            for edge in combinations(triangle, 2)
        }

        assert all(
            edge in edges for edge in combinations(clique, 2)
        )

        incident = sorted(t for t in required if vertex in t)
        for size in range(1, 5):
            assert not any(
                link_contains_k5(subset, vertex)
                for subset in combinations(incident, size)
            )

        print(f"K5_LINK_VERTEX := {vertex}")
        print(f"K5_VERTICES := {clique}")
        print(f"MINIMAL_K5_TETRAHEDRA := {len(witness)}")
        print(f"K5_SUBGRAPH_CERTIFICATE_{vertex} := PASS")

    print("MINIMAL_K5_CERTIFICATE := PASS")
    print("FIXED_WITNESS_MANIFOLD_EXTENSION := EXCLUDED")
    print("GENERAL_THREE_CYCLE_EXCLUSION := OPEN")

    print("PLANARITY_CERTIFICATE := PASS")
    print("FIXED_WITNESS_SIMPLICIAL_MANIFOLD_EXTENSION := EXCLUDED")
    print("CERTIFICATE_SCOPE := EXACT_15_TETRAHEDRON_WITNESS_PATTERN")
    print("GENERAL_REENTRY_CYCLE_EXCLUSION := OPEN")


    def bounded_required_tetrahedra(candidate_faces, cycle_edges):
        result = set()
        for i, face in enumerate(candidate_faces):
            old = cycle_edges[i]
            nxt = cycle_edges[(i + 1) % 3]
            result.update(
                tuple(sorted((*old, *pair)))
                for pair in combinations(face, 2)
            )
            result.update(
                tuple(sorted((*face, x)))
                for x in nxt
            )
        return result

    def bounded_compatible(tets, candidate_faces, cycle_edges):
        if len(tets) != 15:
            return False
        fc = Counter(
            f for t in tets for f in combinations(t, 3)
        )
        ec = Counter(
            e for t in tets for e in combinations(t, 2)
        )
        return (
            all(n <= 2 for n in fc.values())
            and all(fc[f] == 2 for f in candidate_faces)
            and all(ec[e] == 3 for e in cycle_edges)
        )

    def bounded_link_graphs(tets):
        for v in sorted({x for t in tets for x in t}):
            triangles = {
                tuple(x for x in t if x != v)
                for t in tets if v in t
            }
            link_edges = {
                e for t in triangles
                for e in combinations(t, 2)
            }
            nodes = sorted({
                x for t in triangles for x in t
            })
            yield v, nodes, link_edges

    def bounded_has_k5(tets):
        for _, nodes, link_edges in bounded_link_graphs(tets):
            for five in combinations(nodes, 5):
                if all(
                    e in link_edges
                    for e in combinations(five, 2)
                ):
                    return True
        return False

    def bounded_exceeds_planar_bound(tets):
        return any(
            len(nodes) >= 3
            and len(link_edges) > 3 * len(nodes) - 6
            for _, nodes, link_edges in bounded_link_graphs(tets)
        )

    def bounded_trapped_link(tets):
        fc = Counter(
            f for t in tets for f in combinations(t, 3)
        )
        represented_edges = sorted({
            e for t in tets for e in combinations(t, 2)
        })

        for edge in represented_edges:
            graph = defaultdict(set)
            for t in tets:
                if set(edge) <= set(t):
                    a, b = sorted(set(t) - set(edge))
                    graph[a].add(b)
                    graph[b].add(a)

            remaining = set(graph)
            components = []

            while remaining:
                start = min(remaining)
                seen = {start}
                stack = [start]

                while stack:
                    for neighbor in graph[stack.pop()]:
                        if neighbor not in seen:
                            seen.add(neighbor)
                            stack.append(neighbor)

                components.append(tuple(sorted(seen)))
                remaining -= seen

            if len(components) <= 1:
                continue

            closed = [
                component for component in components
                if all(
                    fc[tuple(sorted((*edge, x)))] == 2
                    for x in component
                )
            ]

            if closed:
                fully_saturated = all(
                    fc[tuple(sorted((*edge, x)))] == 2
                    for x in graph
                )
                return "full" if fully_saturated else "mixed"

        return None

    cycle_edges = tuple(edge for _, edge in SITES)
    assert cycle_edges == ((0, 1), (2, 3), (4, 5))

    search_vertices = set(range(11))
    options = [
        list(combinations(
            sorted(
                search_vertices
                - set(cycle_edges[i])
                - set(cycle_edges[(i + 1) % 3])
            ),
            3
        ))
        for i in range(3)
    ]

    bounded_counts = Counter()

    for f0 in options[0]:
        for f1 in options[1]:
            for f2 in options[2]:
                candidate_faces = (f0, f1, f2)
                tets = bounded_required_tetrahedra(
                    candidate_faces, cycle_edges
                )

                if not bounded_compatible(
                    tets, candidate_faces, cycle_edges
                ):
                    continue

                bounded_counts["compatible"] += 1

                if bounded_has_k5(tets):
                    bounded_counts["k5"] += 1
                    continue

                bounded_counts["k5_free"] += 1

                if bounded_exceeds_planar_bound(tets):
                    bounded_counts["planar_bound"] += 1
                    continue

                defect = bounded_trapped_link(tets)

                if defect == "full":
                    bounded_counts["fully_saturated"] += 1
                elif defect == "mixed":
                    bounded_counts["mixed_saturation"] += 1
                else:
                    bounded_counts["surviving"] += 1

    expected_counts = {
        "compatible": 14040,
        "k5": 13440,
        "k5_free": 600,
        "planar_bound": 360,
        "fully_saturated": 60,
        "mixed_saturation": 180,
        "surviving": 0,
    }

    for key, expected_value in expected_counts.items():
        print(
            f"BOUNDED_{key.upper()} := "
            f"{bounded_counts[key]}"
        )
        assert bounded_counts[key] == expected_value

    assert (
        bounded_counts["k5"]
        + bounded_counts["planar_bound"]
        + bounded_counts["fully_saturated"]
        + bounded_counts["mixed_saturation"]
        == bounded_counts["compatible"]
    )

    print("BOUNDED_11_VERTEX_EXCLUSION_CERTIFICATE := PASS")
    print("CERTIFICATE_SCOPE := RELAXED_THREE_STEP_INCIDENCE")
    print("ARBITRARY_VERTEX_COUNT := NOT_TESTED")
    print("FULL_WITNESSED_REENTRY_RELATION := NOT_VERIFIED")
    print("GENERAL_THREE_CYCLE_EXCLUSION := OPEN")

    print('GLOBAL_MANIFOLD_HYPOTHESIS := FAIL')
    print('GLOBAL_JIID := OPEN')


if __name__ == '__main__':
    main()
