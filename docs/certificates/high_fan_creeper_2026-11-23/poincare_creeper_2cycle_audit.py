#!/usr/bin/env python3
"""Exact finite adversarial test of an overstrong Poincare high-fan lemma.

Public repo snapshot: inaciovasquez2020/poincare-new-derivation
branch work/first-nonzero-reentry-20261027
commit 82c5513626533dd1ab925e9529264e2166bd8247

Pure Python 3 standard library; no remote access, no repo mutation, no Lean claims.
"""
import itertools as it
import collections
import json
import platform
from pathlib import Path


def canon(x): return frozenset(x)


def cyclic_6_4():
    # Gale evenness criterion for the facets of cyclic 4-polytope with 6 vertices
    v = range(6)
    result = set()
    for f in it.combinations(v, 4):
        omitted = sorted(set(v) - set(f))
        if all(sum(a < x < b for x in f) % 2 == 0
               for a, b in it.combinations(omitted, 2)):
            result.add(canon(f))
    return result


def cross_4():
    # Boundary of the 4-dimensional cross-polytope: choose one per antipodal pair
    return {canon(f) for f in it.product((0, 1), (2, 3), (4, 5), (6, 7))}

C = cyclic_6_4()
Q = cross_4()
W = {canon(t) for t in ((0, 1, 2, 5), (0, 2, 3, 5),
                         (0, 1, 3, 4), (1, 2, 3, 4))}
E0, E1 = canon((0, 2)), canon((1, 3))
T0 = (canon((0, 1, 2, 5)), canon((0, 2, 3, 5)))
T1 = (canon((0, 1, 3, 4)), canon((1, 2, 3, 4)))


def vertices(k): return set().union(*k)


def faces(k, size):
    return {canon(s) for t in k for s in it.combinations(t, size)}


def degree(k, vertex): return sum(vertex in t for t in k)


def edge_inc(k, e): return sum(e <= t for t in k)


def phi_support(k):
    return sum(abs(degree(k, v) - 4) for v in vertices(k))


def fvector(k):
    return [len(faces(k, j)) for j in range(1, 5)]


def connected_1_skeleton(k):
    verts = vertices(k)
    if not verts: return False
    adjacency = {v: set() for v in verts}
    for t in k:
        for a,b in it.combinations(t,2):
            adjacency[a].add(b)
            adjacency[b].add(a)
    seen = set()
    agenda = [next(iter(verts))]
    while agenda:
        v = agenda.pop()
        if v not in seen:
            seen.add(v)
            agenda.extend(adjacency[v] - seen)
    return len(seen) == len(verts)


def link_sphere_audit(k):
    """Verify every vertex link is a connected closed 2-manifold with chi=2."""
    for v in vertices(k):
        link_faces = {canon(t - {v}) for t in k if v in t}
        assert link_faces and all(len(t) == 3 for t in link_faces)
        f0, f1, f2 = (len(faces(link_faces,j)) for j in (1,2,3))
        assert f0 - f1 + f2 == 2, ('link Euler',v,(f0,f1,f2))
        assert all(sum(e <= t for t in link_faces) == 2
                   for e in faces(link_faces,2)), ('link boundary',v)
        assert connected_1_skeleton(link_faces), ('link connected',v)


def manifold_audit(k):
    assert all(len(t) == 4 for t in k)
    assert all(sum(t <= q for q in k) == 2 for t in faces(k,3))
    assert connected_1_skeleton(k)
    link_sphere_audit(k)


def sum_crosspoly(k, removed_facet):
    """Simplicial connected sum along one 3-simplex, with fresh labels."""
    assert removed_facet in k and len(removed_facet) == 4
    source_facet = canon((0,2,4,6))
    mapping = dict(zip((0,2,4,6), sorted(removed_facet)))
    next_label = max(vertices(k)) + 1
    mapping.update(dict(zip((1,3,5,7), range(next_label,next_label+4))))
    copied = {canon(mapping[v] for v in tet) for tet in (Q - {source_facet})}
    out = (k - {removed_facet}) | copied
    assert len(out) == len(k) + 14
    assert len(vertices(out)) == len(vertices(k)) + 4
    return out


def rank_f2(bitcolumns):
    pivots = {}
    for col in bitcolumns:
        while col:
            p = col.bit_length() - 1
            if p not in pivots:
                pivots[p] = col
                break
            col ^= pivots[p]
    return len(pivots)


def boundary_rank(k, upper_size):
    lower = sorted((tuple(sorted(t)) for t in faces(k,upper_size-1)))
    upper = sorted((tuple(sorted(t)) for t in faces(k,upper_size)))
    idx = {f:i for i,f in enumerate(lower)}
    return rank_f2([sum(1 << idx[f] for f in it.combinations(u,upper_size-1))
                    for u in upper])


def mod2_betti(k):
    f0,f1,f2,f3 = fvector(k)
    r1,r2,r3 = (boundary_rank(k, j) for j in (2,3,4))
    return {'boundary_ranks': [r1,r2,r3],
            'betti': [f0-r1,f1-r1-r2,f2-r2-r3,f3-r3]}


def legal_32(k):
    """Exactly-three edge star with absent replacement triangle."""
    result=[]
    triangular_faces=faces(k,3)
    for edge in faces(k,2):
        star={t for t in k if edge<=t}
        if len(star)!=3: continue
        remaining=vertices(star)-edge
        if len(remaining)!=3: continue
        if {t-edge for t in star} != {canon(a) for a in it.combinations(remaining,2)}:
            continue
        if canon(remaining) in triangular_faces:
            continue
        result.append((edge,canon(remaining),star))
    return sorted(result,key=lambda rec:tuple(sorted(rec[0])))


def legal_23(k):
    """Pair of tetrahedra with exactly shared face and absent new edge."""
    incidents=collections.defaultdict(list)
    all_edges=faces(k,2)
    for tet in k:
        for f in it.combinations(tet,3): incidents[canon(f)].append(tet)
    result=[]
    for face,tets in incidents.items():
        if len(tets)!=2: continue
        tips=canon(tets[0]^tets[1])
        if len(tips)==2 and tips not in all_edges:
            result.append((face,tips))
    return result


def check_return(k):
    assert W<=k
    assert all(edge_inc(k,e)>=4 for e in (E0,E1))
    # T0 old 02 -> chord 13 with transverse 5; T1 old 13 -> chord 02 with transverse 4
    assert all(t in k for t in T0+T1)
    assert T0[0]&T0[1] == canon((0,2,5))
    assert T1[0]&T1[1] == canon((1,3,4))
    assert canon((1,3)) <= T1[0] and not E0 <= T1[0]  # Off-edge witness for T0
    assert E0 <= T0[0] and not E1 <= T0[0]             # Off-edge witness for T1
    assert 5!=4


def run(njoins=12):
    assert len(C)==9 and len(Q)==16
    manifold_audit(C); manifold_audit(Q)
    k=C
    stages=[]
    for n in range(1,njoins+1):
        target = E1 if n%2==1 else E0
        if n == 1:
            facet=canon((0,1,2,3))
        else:
            choices=[t for t in k if target <= t and t not in W]
            assert choices, ('no safe facet',n)
            facet=min(choices,key=lambda x:tuple(sorted(x)))
        k=sum_crosspoly(k,facet)
        manifold_audit(k);check_return(k)
        assert min(degree(k,v) for v in vertices(k)) >= 6
        assert fvector(k) == [6+4*n,15+18*n,18+28*n,9+14*n]
        assert phi_support(k)==12+40*n
        stages.append({'joins':n, 'fvector':fvector(k),
                       'incidence_02':edge_inc(k,E0),
                       'incidence_13':edge_inc(k,E1),
                       'min_vertex_degree':min(degree(k,v) for v in vertices(k)),
                       'legal_32':len(legal_32(k))})
        if n==1:
            first=k.copy()
    assert fvector(first)==[10,33,46,23]
    assert len(legal_23(first))==32
    assert phi_support(first)==52
    assert mod2_betti(first)=={'boundary_ranks':[9,24,22], 'betti':[1,0,0,1]}
    reductions=[]
    for edge,ring,star in legal_32(first):
        assert len(star & W)==1
        after=(first-star)|{canon(set(ring)|{v}) for v in edge}
        assert phi_support(after)==48
        manifold_audit(after)
        reductions.append({'edge':sorted(edge), 'ring':sorted(ring),
                           'destroyed_witness':sorted(next(iter(star & W))),
                           'phi_after':phi_support(after)})
    assert len(reductions)==4

    # Stronger CREEPER fixture: inflate all four residual incidence-three edges
    # without deleting any of the four transition tetrahedra.
    stalled = sum_crosspoly(first, canon((0,1,4,5)))
    assert canon((2,3,4,5)) in stalled
    stalled = sum_crosspoly(stalled, canon((2,3,4,5)))
    manifold_audit(stalled);check_return(stalled)
    assert fvector(stalled)==[18,69,102,51]
    assert min(degree(stalled,v) for v in vertices(stalled))==8
    assert min(edge_inc(stalled,e) for e in faces(stalled,2))==4
    assert phi_support(stalled)==132
    assert len(legal_32(stalled))==0
    legal23stalled = legal_23(stalled)
    assert len(legal23stalled)==96
    # Enumerate ALL legal 2->3 moves, independently checking their potential.
    for common,tips in legal23stalled:
        old={t for t in stalled if common<=t}
        assert len(old)==2
        new={canon(set(tips)|set(s)) for s in it.combinations(common,2)}
        out=(stalled-old)|new
        assert len(out)==len(stalled)+1
        assert phi_support(out)==136
        manifold_audit(out)
    # Enumerate ALL 1->4 stellar subdivisions, independently checking Phi.
    for source in stalled:
        fresh=max(vertices(stalled))+1
        new={canon(set(s)|{fresh}) for s in it.combinations(source,3)}
        out=(stalled-{source})|new
        assert len(out)==len(stalled)+3
        assert phi_support(out)==140
        manifold_audit(out)
    stalled_audit={'fvector':fvector(stalled),
                   'phi_support':phi_support(stalled),
                   'min_vertex_degree':min(degree(stalled,v) for v in vertices(stalled)),
                   'min_edge_incidence':min(edge_inc(stalled,e) for e in faces(stalled,2)),
                   'return_incidences':[edge_inc(stalled,E0),edge_inc(stalled,E1)],
                   'legal_32':len(legal_32(stalled)),
                   'legal_23':len(legal23stalled),
                   'legal_23_phi_after_all':[136]*len(legal23stalled),
                   'move14_count_checked':len(stalled),
                   'move14_phi_after':140,
                   'homology':mod2_betti(stalled),
                   'monotone_single_move_descent_possible':False}

    return {'status':'COMPUTATION_PASS', 'python':platform.python_version(),
            'source_commit':'82c5513626533dd1ab925e9529264e2166bd8247',
            'method':'pure Python exact set arithmetic and GF(2) elimination',
            'initial_cyclic_sphere_tetrahedra':len(C),
            'initial_crosspoly_sphere_tetrahedra':len(Q),
            'first_connected_sum':{'fvector':fvector(first),
                                   'vertex_degrees':{str(v):degree(first,v) for v in sorted(vertices(first))},
                                   'phi_support':phi_support(first),
                                   'mod2_homology':mod2_betti(first),
                                   'legal_23':len(legal_23(first)),
                                   'legal_32':len(legal_32(first)),
                                   'different_transverse_pair':[5,4],
                                   'edge_incidences':[edge_inc(first,E0),edge_inc(first,E1)],
                                   'legal_32_reductions':reductions},
            'escalation':stages,
            'no_immediate_descent_sphere':stalled_audit,
            'scope':'finite checks plus independent mathematical connected-sum induction; Lean NOT_RUN'}


if __name__=='__main__':
    receipt=run()
    print(json.dumps(receipt,indent=2,sort_keys=True))
