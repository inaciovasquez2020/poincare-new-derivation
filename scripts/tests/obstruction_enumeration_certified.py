import random
from collections import defaultdict
from collections import Counter
import itertools
from fractions import Fraction

TET_FACES = (
    (1, 2, 3),
    (0, 2, 3),
    (0, 1, 3),
    (0, 1, 2),
)

ORIENTED_TRI_PERMS = [
    (0, 1, 2),
    (1, 2, 0),
    (2, 0, 1),
    (0, 2, 1),
    (2, 1, 0),
    (1, 0, 2),
]

ODD_TRI_PERMS = [p for p in ORIENTED_TRI_PERMS if (p in [(0, 2, 1), (2, 1, 0), (1, 0, 2)])]


class DSU:
    def __init__(self):
        self.parent = {}
        self.rank = {}

    def add(self, x):
        if x not in self.parent:
            self.parent[x] = x
            self.rank[x] = 0

    def find(self, x):
        self.add(x)
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        if self.rank[ra] < self.rank[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        if self.rank[ra] == self.rank[rb]:
            self.rank[ra] += 1


def tet_face_vertices(face_idx):
    return TET_FACES[face_idx]


def all_faces(num_tets):
    for t in range(num_tets):
        for f in range(4):
            yield (t, f)


def pairings_of_faces(faces):
    faces = list(faces)
    if not faces:
        yield []
        return
    first = faces[0]
    for i in range(1, len(faces)):
        second = faces[i]
        rest = faces[1:i] + faces[i + 1 :]
        for tail in pairings_of_faces(rest):
            yield [(first, second)] + tail


def canonical_pairing_key(pairing):
    norm = sorted(tuple(sorted(p)) for p in pairing)
    return tuple(norm)


def gluing_maps_for_pairing(pairing):
    choices = []
    for _ in pairing:
        perms = list(ODD_TRI_PERMS)
        perms.sort(key=lambda p: len(set(p)), reverse=True)
        choices.append(perms)
    for maps in itertools.product(*choices):
        yield list(zip(pairing, maps))


def build_complex(num_tets, gluing_data, debug=False):
    dsu = DSU()
    partial_vertex_counts = []
    for t in range(num_tets):
        for v in range(4):
            dsu.add((t, v))
    face_partner = {}
    for ((a, b), perm) in gluing_data:
        (t1, f1), (t2, f2) = a, b
        fv1 = tet_face_vertices(f1)
        fv2 = tet_face_vertices(f2)

        for i in range(3):
            dsu.union((t1, fv1[i]), (t2, fv2[perm[i]]))

        # track partial vertex classes
        current_classes = set(dsu.find((t, v)) for t in range(num_tets) for v in range(4))
        partial_vertex_counts.append(len(current_classes))

        # early pruning: collapse below 4 total vertices
        if len(current_classes) < 5:
            if debug:
                print({
                    "early_prune": True,
                    "reason": "vertex_collapse",
                    "partial_vertex_counts": partial_vertex_counts
                })
            return None

        face_partner[(t1, f1)] = ((t2, f2), perm)
        face_partner[(t2, f2)] = ((t1, f1), perm)
    vertex_classes = {}
    rep_to_vid = {}
    next_vid = 0
    for t in range(num_tets):
        for v in range(4):
            r = dsu.find((t, v))
            if r not in rep_to_vid:
                rep_to_vid[r] = next_vid
                next_vid += 1
            vertex_classes[(t, v)] = rep_to_vid[r]
    tets = []
    degenerate_tets = []
    for t in range(num_tets):
        tet = tuple(vertex_classes[(t, v)] for v in range(4))
        if len(set(tet)) < 4:
            degenerate_tets.append((t, tet))
        tets.append(tet)

    # enforce injectivity per tetrahedron
    if degenerate_tets:
        if debug:
            print({
                "reject_injective_violation": True,
                "degenerate_tets": degenerate_tets
            })
        return None

    if debug:
        cls = {}
        for tv, vid in vertex_classes.items():
            cls.setdefault(vid, []).append(tv)
        print({
            "debug_build_complex": True,
            "num_tets": num_tets,
            "num_vertex_classes": len(cls),
            "vertex_classes": {k: sorted(v) for k, v in sorted(cls.items())},
            "partial_vertex_counts": partial_vertex_counts,
            "degenerate_tets": degenerate_tets,
            "all_tets": tets,
            "rejection_reason": "degenerate_tetrahedra" if degenerate_tets else "accepted"
        })

    if degenerate_tets:
        return {
            "num_tets": num_tets,
            "tets": tuple(tets),
            "face_partner": face_partner,
            "vertex_classes": vertex_classes,
            "degenerate_tets": tuple(degenerate_tets),
            "debug_rejected": True,
        }
    return {
        "num_tets": num_tets,
        "tets": tuple(tets),
        "face_partner": face_partner,
        "vertex_classes": vertex_classes,
    }


def face_multiset(complex_):
    cnt = Counter()
    for tet in complex_["tets"]:
        for face in itertools.combinations(tet, 3):
            cnt[tuple(sorted(face))] += 1
    return cnt


def edge_multiset(complex_):
    cnt = Counter()
    for tet in complex_["tets"]:
        for e in itertools.combinations(tet, 2):
            cnt[tuple(sorted(e))] += 1
    return cnt


def vertex_degree_tetra(complex_):
    cnt = Counter()
    for tet in complex_["tets"]:
        for v in tet:
            cnt[v] += 1
    return cnt


def Phi(complex_):
    deg = vertex_degree_tetra(complex_)
    return sum(abs(deg[v] - 6) for v in deg)


def closed_pseudomanifold(complex_):
    fc = face_multiset(complex_)
    return all(v == 2 for v in fc.values())


def link_graph_of_vertex(complex_, v):
    nbr_edges = Counter()
    for tet in complex_["tets"]:
        if v not in tet:
            continue
        others = [x for x in tet if x != v]
        for e in itertools.combinations(sorted(others), 2):
            nbr_edges[e] += 1
    verts = set()
    adj = defaultdict(set)
    for (a, b), m in nbr_edges.items():
        if m == 0:
            continue
        verts.add(a)
        verts.add(b)
        adj[a].add(b)
        adj[b].add(a)
    return verts, adj, nbr_edges


def is_sphere_link(complex_, v):
    verts, adj, edge_mult = link_graph_of_vertex(complex_, v)
    if not verts:
        return False
    if any(len(adj[x]) != 3 for x in verts):
        return False
    seen = set()
    q = deque([next(iter(verts))])
    while q:
        x = q.popleft()
        if x in seen:
            continue
        seen.add(x)
        for y in adj[x]:
            if y not in seen:
                q.append(y)
    if seen != verts:
        return False
    E = sum(len(adj[x]) for x in verts) // 2
    V = len(verts)
    F = sum(1 for tet in complex_["tets"] if v in tet)
    return V - E + F == 2


def is_closed_3_manifold(complex_):
    if complex_ is None:
        return False
    if not closed_pseudomanifold(complex_):
        return False
    verts = sorted({v for tet in complex_["tets"] for v in tet})
    return all(is_sphere_link(complex_, v) for v in verts)


def one_skeleton(complex_):
    verts = sorted({v for tet in complex_["tets"] for v in tet})
    adj = defaultdict(set)
    edges = set()
    for tet in complex_["tets"]:
        for a, b in itertools.combinations(sorted(tet), 2):
            adj[a].add(b)
            adj[b].add(a)
            edges.add((a, b))
    return verts, sorted(edges), adj


def triangles(complex_):
    tris = set()
    for tet in complex_["tets"]:
        for tri in itertools.combinations(sorted(tet), 3):
            tris.add(tri)
    return sorted(tris)


def rank_mod2(rows, ncols):
    rows = [list(r) for r in rows if any(r)]
    rank = 0
    col = 0
    while col < ncols and rank < len(rows):
        piv = None
        for i in range(rank, len(rows)):
            if rows[i][col] % 2 == 1:
                piv = i
                break
        if piv is None:
            col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i][col] % 2 == 1:
                rows[i] = [(a ^ b) for a, b in zip(rows[i], rows[rank])]
        rank += 1
        col += 1
    return rank


def certified_invariant_H1_mod2_zero(complex_):
    verts, edges, _ = one_skeleton(complex_)
    vidx = {v: i for i, v in enumerate(verts)}
    eidx = {e: i for i, e in enumerate(edges)}

    d1 = []
    for e in edges:
        row = [0] * len(verts)
        a, b = e
        row[vidx[a]] = 1
        row[vidx[b]] ^= 1
        d1.append(row)

    d2 = []
    for tri in triangles(complex_):
        row = [0] * len(edges)
        for e in itertools.combinations(tri, 2):
            row[eidx[tuple(sorted(e))]] ^= 1
        d2.append(row)

    rank_d1 = rank_mod2(d1, len(verts))
    rank_d2 = rank_mod2(d2, len(edges))
    beta1 = len(edges) - rank_d1 - rank_d2
    return beta1 == 0


def certified_filter(complex_):
    return is_closed_3_manifold(complex_) and certified_invariant_H1_mod2_zero(complex_)


def edge_link_vertices(complex_, edge):
    opp = []
    a, b = edge
    star = []
    for tet in complex_["tets"]:
        if a in tet and b in tet:
            star.append(tet)
            opp.append(tuple(sorted([x for x in tet if x not in edge])))
    if len(star) != 3:
        return None
    opp_vertices = []
    for pair in opp:
        if len(pair) != 2:
            return None
        for x in pair:
            opp_vertices.append(x)
    cnt = Counter(opp_vertices)
    cyc = [v for v, c in cnt.items() if c == 2]
    if len(cyc) != 3:
        return None
    return tuple(sorted(cyc)), tuple(star)


def exact_3_to_2_move(complex_, edge):
    link = edge_link_vertices(complex_, edge)
    if link is None:
        return None
    cyc, star = link
    a, b = edge
    new_tets = [tet for tet in complex_["tets"] if tet not in star]
    x, y, z = cyc
    t1 = tuple(sorted((a, x, y, z)))
    t2 = tuple(sorted((b, x, y, z)))
    if len(set(t1)) < 4 or len(set(t2)) < 4:
        return None
    new_tets.extend([t1, t2])
    candidate = {"num_tets": len(new_tets), "tets": tuple(new_tets)}
    if not is_closed_3_manifold(candidate):
        return None
    return candidate


def delta_phi_3_to_2(complex_, edge):
    moved = exact_3_to_2_move(complex_, edge)
    if moved is None:
        return None
    return Phi(moved) - Phi(complex_)


def generate_face_paired_complexes(num_tets, max_pairings=None, max_gluings_per_pairing=None):
    faces = list(all_faces(num_tets))
    seen_pairings = set()
    print({"faces_count": 4 * num_tets})
    yielded = 0
    for pairing in pairings_of_faces(faces):
        print({"pairings_generated": len(seen_pairings)})
        key = canonical_pairing_key(pairing)
        if key in seen_pairings:
            continue
        seen_pairings.add(key)
        gcount = 0
        for gluing_data in gluing_maps_for_pairing(pairing):
            complex_ = build_complex(num_tets, gluing_data, debug=(yielded < 10))
            if complex_ is not None:
                if "partial_vertex_counts" in complex_:
                    surviving_sequences.append(complex_["partial_vertex_counts"])
                yield complex_
                yielded += 1
            gcount += 1
            if max_gluings_per_pairing is not None and gcount >= max_gluings_per_pairing:
                break
        if max_pairings is not None and len(seen_pairings) >= max_pairings:
            break


def canonical_complex_key(complex_):
    tets = tuple(sorted(tuple(sorted(t)) for t in complex_["tets"]))
    return tets


def run(num_tets_max=3, max_pairings=None, max_gluings_per_pairing=None):
    seen = set()
    obstructions = []
    tested = 0
    certified = 0

    for num_tets in range(1, num_tets_max + 1):
        for complex_ in generate_face_paired_complexes(
            num_tets,
            max_pairings=max_pairings,
            max_gluings_per_pairing=max_gluings_per_pairing,
        ):
            key = canonical_complex_key(complex_)
            if key in seen:
                continue
            seen.add(key)
            tested += 1

            if complex_.get("debug_rejected"):
                print({
                    "debug_candidate": True,
                    "num_tets": complex_["num_tets"],
                    "degenerate_tets": complex_.get("degenerate_tets", ()),
                    "num_distinct_vertices": len({v for tet in complex_["tets"] for v in tet}),
                    "collapsed_below_4_classes": len({v for tet in complex_["tets"] for v in tet}) < 4,
                })
                continue
            if not certified_filter(complex_):
                print({
                    "debug_filter_reject": True,
                    "num_tets": complex_["num_tets"],
                    "closed_3_manifold": is_closed_3_manifold(complex_),
                    "H1_mod2_zero": certified_invariant_H1_mod2_zero(complex_),
                    "tets": complex_["tets"],
                })
                continue
            certified += 1

            edeg = edge_multiset(complex_)
            deltas = []
            for e, d in sorted(edeg.items()):
                if d == 3:
                    dphi = delta_phi_3_to_2(complex_, e)
                    if dphi is not None:
                        deltas.append((e, dphi))

            if deltas and all(dphi >= 0 for _, dphi in deltas):
                obstructions.append(
                    {
                        "tets": complex_["tets"],
                        "phi": Phi(complex_),
                        "moves": deltas,
                    }
                )

    print(
        {
            "tested_complexes": tested,
            "certified_complexes": certified,
            "obstructions": len(obstructions),
        }
    )
    print({"surviving_sequences": True})
    for i, obs in enumerate(obstructions[:10], 1):
        print(
            {
                "index": i,
                "phi": obs["phi"],
                "tets": obs["tets"],
                "moves": obs["moves"],
            }
        )


if __name__ == "__main__":
    run()
