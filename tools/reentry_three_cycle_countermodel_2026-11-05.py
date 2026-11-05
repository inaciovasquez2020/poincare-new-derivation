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

    print('GLOBAL_MANIFOLD_HYPOTHESIS := FAIL')
    print('GLOBAL_JIID := OPEN')


if __name__ == '__main__':
    main()
