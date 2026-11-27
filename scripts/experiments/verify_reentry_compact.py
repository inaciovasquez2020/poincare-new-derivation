#!/usr/bin/env python3
"""Finite witnessed-reentry/ZMod(2) cocycle audit. Standard library only.
Does not claim universal proof or validate the historical Pachner trace.
"""
import collections, itertools, json, pathlib, sys
p=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else pathlib.Path(__file__).with_name('nonsimplyconnected_witness_compact.json')
r=json.loads(p.read_text())
T={frozenset(t) for t in r['tetrahedra']}
assert len(T)==51 and all(len(t)==4 for t in T)
F=collections.Counter(frozenset(z) for t in T for z in itertools.combinations(t,3))
E=collections.Counter(frozenset(z) for t in T for z in itertools.combinations(t,2))
assert len(F)==102 and len(E)==67 and all(c==2 for c in F.values())
w=r['witness']; d,e=w['old_edge'];a,b,c=w['old_face'];x,y=w['complement_vertices']
assert E[frozenset((d,e))]==3
assert {frozenset(t) for t in w['source_tets']} == {frozenset((d,e))|frozenset(z) for z in itertools.combinations((a,b,c),2)}
assert all(frozenset(t) in T for t in w['source_tets'])
assert {frozenset(t) for t in w['obstructing_face_tets']} == {frozenset((a,b,c,x)),frozenset((a,b,c,y))}
assert all(frozenset(t) in T for t in w['obstructing_face_tets'])
assert frozenset((x,y)) != frozenset((d,e)) and E[frozenset((x,y))]==3
l=w['new_link']; assert len(set(l))==3
assert {frozenset(t) for t in w['new_tets']} == {frozenset((x,y))|frozenset(z) for z in itertools.combinations(l,2)}
assert all(frozenset(t) in T for t in w['new_tets'])
assert {frozenset(t) for t in w['new_obstructing_face_tets']} == {frozenset(l)|frozenset((z,)) for z in set().union(*[set(t) for t in w['new_obstructing_face_tets']])-set(l)}
assert all(frozenset(t) in T for t in w['new_obstructing_face_tets'])
C=[frozenset(z) for z in r['cycle']]; W={frozenset(z) for z in r['cocycle']}
assert set(C)=={frozenset((x,a)),frozenset((a,y)),frozenset((x,y))}
assert all(n%2==0 for n in collections.Counter(v for edge in C for v in edge).values())
assert W <= set(E) and len(W)==12
assert all(sum(frozenset(z) in W for z in itertools.combinations(f,2))%2==0 for f in F)
assert sum(edge in W for edge in C)%2==1
print(json.dumps({'status':'COMPUTATION_PASS','tetrahedra':len(T),'faces':len(F),'edges':len(E),'cocycle_edges':len(W),'pairing':1,'witness':True}))
