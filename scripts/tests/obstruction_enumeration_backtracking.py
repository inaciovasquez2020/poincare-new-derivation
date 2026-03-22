import itertools
import math
from collections import defaultdict

TET_FACES = (
    (1, 2, 3),
    (0, 2, 3),
    (0, 1, 3),
    (0, 1, 2),
)

ODD_TRI_PERMS = [
    (0, 2, 1),
    (2, 1, 0),
    (1, 0, 2),
]

class DSU:
    def __init__(self, n):
        self.parent = list(range(n))
        self.rank = [0] * n

    def copy(self):
        d = DSU(0)
        d.parent = self.parent[:]
        d.rank = self.rank[:]
        return d

    def find(self, x):
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

def tv_index(t, v):
    return 4 * t + v

def tet_face_vertices(face_idx):
    return TET_FACES[face_idx]

def all_faces(num_tets):
    return [(t, f) for t in range(num_tets) for f in range(4)]

def face_pairings_dfs(faces):
    if not faces:
        yield []
        return
    a = faces[0]
    for i in range(1, len(faces)):
        b = faces[i]
        rest = faces[1:i] + faces[i+1:]
        for tail in face_pairings_dfs(rest):
            yield [(a, b)] + tail

def current_class_count(dsu):
    return len({dsu.find(i) for i in range(len(dsu.parent))})

def tetra_classes(dsu, num_tets):
    out = {}
    for t in range(num_tets):
        cls = tuple(dsu.find(tv_index(t, v)) for v in range(4))
        out[t] = cls
    return out

def tetra_injective(dsu, num_tets):
    for t in range(num_tets):
        cls = [dsu.find(tv_index(t, v)) for v in range(4)]
        if len(set(cls)) < 4:
            return False
    return True

def entropy_score(dsu):
    roots = [dsu.find(i) for i in range(len(dsu.parent))]
    counts = defaultdict(int)
    for r in roots:
        counts[r] += 1
    n = len(roots)
    h = 0.0
    for c in counts.values():
        p = c / n
        h -= p * math.log(max(p, 1e-12))
    return h

def apply_pairing_step(dsu, pair, perm):
    d2 = dsu.copy()
    (t1, f1), (t2, f2) = pair
    fv1 = tet_face_vertices(f1)
    fv2 = tet_face_vertices(f2)
    for i in range(3):
        d2.union(tv_index(t1, fv1[i]), tv_index(t2, fv2[perm[i]]))
    return d2

def choose_perm_order(dsu, pair):
    scored = []
    for perm in ODD_TRI_PERMS:
        d2 = apply_pairing_step(dsu, pair, perm)
        if not tetra_injective(d2, NUM_TETS):
            continue
        cc = current_class_count(d2)
        if cc < 4:
            continue
        scored.append((entropy_score(d2), cc, perm))
    scored.sort(reverse=True)
    return [perm for _, _, perm in scored]

def search_first_noncollapsing(pairing, num_tets):
    global NUM_TETS
    NUM_TETS = num_tets
    dsu0 = DSU(4 * num_tets)
    path = []
    partial_counts = [current_class_count(dsu0)]
    best_depth = 0
    best_min_count = float('inf')
    cache = set()

    def dsu_signature(dsu):
        return tuple(sorted(dsu.find(i) for i in range(len(dsu.parent))))

    def dfs(i, dsu):
        nonlocal best_depth, best_min_count

        sig = (i, dsu_signature(dsu))
        if sig in cache:
            cache.add(sig)
        return None

        if i > best_depth:
            best_depth = i
        best_min_count = min(best_min_count, min(partial_counts))

        if i == len(pairing):
            return {
                "pairing": pairing,
                "perms": path[:],
                "partial_vertex_counts": partial_counts[:],
                "tetra_classes": tetra_classes(dsu, num_tets),
                "best_depth": best_depth,
                "best_min_count": best_min_count,
            }
        pair = pairing[i]
        perm_order = choose_perm_order(dsu, pair, i)
        for perm in perm_order:
            d2 = apply_pairing_step(dsu, pair, perm)
            cc = current_class_count(d2)

            if i == 0:
                if cc < 3:
                    continue
                print({"first_valid_expansion": True, "cc": cc})
            else:
                if cc < 4:
                    continue
                if not tetra_injective(d2, num_tets):
                    continue

            path.append((pair, perm))
            partial_counts.append(cc)
            out = dfs(i + 1, d2)
            if out is not None:
                return out
            partial_counts.pop()
            path.pop()
        cache.add(sig)
        return None

    result = dfs(0, dsu0)
    if result is None:
        print({
            "best_partial_depth": best_depth,
            "best_min_vertex_count": best_min_count
        })
    return result

def run(num_tets=3, max_pairings=5000):
    faces = all_faces(num_tets)
    checked = 0
    for pairing in face_pairings_dfs(faces):
        checked += 1
        result = search_first_noncollapsing(pairing, num_tets)
        if result is not None:
            print({
                "found": True,
                "pairings_checked": checked,
                "partial_vertex_counts": result["partial_vertex_counts"],
                "pairing_length": len(result["pairing"]),
                "perms": result["perms"],
                "tetra_classes": result["tetra_classes"],
            })
            return
        if checked >= max_pairings:
            break
    print({
        "found": False,
        "pairings_checked": checked,
    })

if __name__ == "__main__":
    run()
