#!/usr/bin/env python3
"""Exact F2 dual-graph obstruction for a witnessed reentry.
Standard library only. No Lean or universal theorem claimed.
Input: earlier archived adversarial receipt with `final_tetrahedra`, `witness`.
"""
import collections
import itertools
import json
import pathlib
import sys


def faces(t):
    return [frozenset(c) for c in itertools.combinations(sorted(t), 3)]


def face_index(tets):
    idx = collections.defaultdict(list)
    for i, tet in enumerate(tets):
        assert len(tet) == 4
        for f in faces(tet):
            idx[f].append(i)
    assert all(len(ids) == 2 for ids in idx.values()), 'not closed triangular incidence'
    return idx


def dual_path(tets, index, start, end, forbidden):
    graph = [[] for _ in tets]
    for f, (u, v) in index.items():
        if f not in forbidden:
            graph[u].append((v, f))
            graph[v].append((u, f))
    pred = {start: None}
    queue = collections.deque([start])
    while queue and end not in pred:
        u = queue.popleft()
        for v, face in sorted(graph[u], key=lambda z: (z[0], sorted(z[1]))):
            if v not in pred:
                pred[v] = (u, face)
                queue.append(v)
    if end not in pred:
        return None
    rev = []
    v = end
    while pred[v] is not None:
        u, face = pred[v]
        rev.append([u, v, sorted(face)])
        v = u
    return rev[::-1]


def mod2_in_span(columns, target):
    basis = {}
    for col in columns:
        c = col
        while c:
            k = c.bit_length() - 1
            if k in basis:
                c ^= basis[k]
            else:
                basis[k] = c
                break
    c = target
    while c:
        k = c.bit_length() - 1
        if k not in basis:
            return False
        c ^= basis[k]
    return True


def evaluate(tetrahedra, source_face, x, y, q, expected_nonboundary):
    tets = [frozenset(t) for t in tetrahedra]
    assert len(tets) == len(set(tets))
    index = face_index(tets)
    a, b, c = source_face
    s = {frozenset(f) for f in itertools.combinations(sorted((a, b, c, q)), 3)}
    assert all(f in index for f in s)
    tx = tets.index(frozenset((a, b, c, x)))
    ty = tets.index(frozenset((a, b, c, y)))
    assert tx != ty
    assert set(index[frozenset((a, b, c))]) == {tx, ty}
    p = dual_path(tets, index, tx, ty, s)
    flist = sorted(index, key=lambda f: tuple(sorted(f)))
    fm = {f: i for i, f in enumerate(flist)}
    columns = [sum(1 << fm[f] for f in faces(t)) for t in tets]
    target = sum(1 << fm[f] for f in s)
    bounds = mod2_in_span(columns, target)
    assert bounds != expected_nonboundary
    assert (p is not None) == expected_nonboundary
    if p is not None:
        assert p[0][0] == tx and p[-1][1] == ty
        for u, v, f in p:
            assert frozenset(f) not in s
            assert set(index[frozenset(f)]) == {u, v}
    return {
        'sphere_apex': q,
        'sphere_faces': [sorted(f) for f in sorted(s, key=lambda f: tuple(sorted(f)))],
        'source_tetrahedron_index': tx,
        'target_tetrahedron_index': ty,
        'dual_path_avoiding_sphere': p,
        'dual_cycle_odd_crossings': 1 if p is not None else None,
        'sphere_is_tetrahedron_3_boundary': bounds,
        'result': 'COMPUTATION_PASS',
    }


def main():
    filename = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path(__file__).with_name('poincare_reentry_adversarial_receipt.json')
    r = json.loads(filename.read_text())
    w = r['witness']
    a, b, c = w['old_face']
    d, e = w['old_edge']
    x, y = w['complement_vertices']
    assert {x, y} != {d, e} and x != y
    qlist = sorted({d, e} - {x, y})
    assert qlist
    results = [evaluate(r['final_tetrahedra'], [a,b,c], x, y, q, True) for q in qlist]
    # Negative control: a genuine tetrahedral boundary in the standard 3-sphere.
    std_tets = [sorted(set(range(5)) - {v}) for v in range(5)]
    control = evaluate(std_tets, [0,1,2], 3,4,3,False)
    report = {
        'status':'COMPUTATION_PASS',
        'claim':'finite odd-dual-cycle non-3-boundary certificate, NOT universal Lean theorem',
        'source': str(filename),
        'number_tetrahedra':len(r['final_tetrahedra']),
        'witnesses':results,
        'negative_control_boundary4simplex':control,
        'global_h2_vanishing_bridge':'NOT_RUN',
        'lean':'NOT_RUN',
    }
    out = pathlib.Path(__file__).with_name('poincare_reentry_dual_path_receipt.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({
        'status':report['status'],
        'q':qlist,
        'dual_path_lengths':[len(z['dual_path_avoiding_sphere']) for z in results],
        'all_spheres_nonbounding':all(not z['sphere_is_tetrahedron_3_boundary'] for z in results),
        'negative_control_bounds':control['sphere_is_tetrahedron_3_boundary'],
        'receipt':str(out)
    }))

if __name__ == '__main__':
    main()