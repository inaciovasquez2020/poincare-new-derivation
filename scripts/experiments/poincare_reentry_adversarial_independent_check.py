#!/usr/bin/env python3
"""Independent validation of a stored bistellar trace and mod-two cocycle.
Does not import the witness generator. Python standard library only.
"""
import json,sys,itertools,collections,hashlib,pathlib
P=(pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else
   pathlib.Path(__file__).resolve().parents[2] / 'docs/certificates/reentry_2026-11-15/poincare_reentry_adversarial_receipt.json')
r=json.loads(P.read_text())
def product(m=4):
 t=set()
 for p in range(m):
  for a,b,c in itertools.combinations(range(4),3):
   x=[a*m+p,b*m+p,c*m+p];y=[a*m+(p+1)%m,b*m+(p+1)%m,c*m+(p+1)%m]
   for k in range(3):t.add(frozenset(x[:k+1]+y[k:]))
 return t
T=product()
assert len(T)==48
for i,move in enumerate(r['moves']):
 typ=move['move'];old=[frozenset(t) for t in move['removed']];new=[frozenset(t) for t in move['added']]
 assert len(old)==(2 if typ==23 else 3),(i,'bad old count')
 assert len(new)==(3 if typ==23 else 2),(i,'bad new count')
 assert all(t in T for t in old),(i,'old tetra not present')
 assert all(t not in T for t in new),(i,'new tetra already present')
 assert len(set(old))==len(old) and len(set(new))==len(new)
 if typ==23:
  face=frozenset(move['face']);edge=frozenset(move['edge']);assert len(face)==3 and len(edge)==2
  assert face.isdisjoint(edge)
  assert set(old)=={face|frozenset((v,)) for v in edge}
  assert set(new)=={edge|frozenset(z) for z in itertools.combinations(face,2)}
  assert not any(edge<=t for t in T)
 else:
  face=frozenset(move['face']);edge=frozenset(move['edge']);assert len(face)==3 and len(edge)==2
  assert face.isdisjoint(edge)
  assert set(old)=={edge|frozenset(z) for z in itertools.combinations(face,2)}
  assert set(new)=={face|frozenset((v,)) for v in edge}
  assert not any(face<=t for t in T)
 T=(T-set(old))|set(new)
 # Independently verify closed triangular incidence after every move.
 f=collections.Counter(frozenset(z) for t in T for z in itertools.combinations(t,3))
 assert f and all(c==2 for c in f.values()),(i,'bad closure')
assert sorted(map(lambda t:sorted(t),T))==r['final_tetrahedra']
f=collections.Counter(frozenset(z) for t in T for z in itertools.combinations(t,3))
e=collections.Counter(frozenset(z) for t in T for z in itertools.combinations(t,2))
w=r['witness'];d,e0=w['old_edge'];a,b,c=w['old_face'];x,y=w['complement_vertices']
assert e[frozenset((d,e0))]==3
assert {frozenset(t) for t in w['source_tets']}=={frozenset((d,e0,a,b)),frozenset((d,e0,b,c)),frozenset((d,e0,a,c))}
assert all(frozenset(t) in T for t in w['source_tets'])
assert f[frozenset((a,b,c))]==2
assert {frozenset(t) for t in w['obstructing_face_tets']}=={frozenset((a,b,c,x)),frozenset((a,b,c,y))}
assert frozenset((x,y))!=frozenset((d,e0))
assert e[frozenset((x,y))]==3
newlink=frozenset(w['new_link']);assert len(newlink)==3
assert {frozenset(t) for t in w['new_tets']}=={frozenset((x,y))|frozenset(z) for z in itertools.combinations(newlink,2)}
assert all(frozenset(t) in T for t in w['new_tets'])
assert f[newlink]==2
C=[frozenset(z) for z in r['chain_audit']['three_edge_cycle']]
assert set(C)=={frozenset((x,a)),frozenset((a,y)),frozenset((x,y))}
verts=collections.Counter(v for ed in C for v in ed)
assert all(n%2==0 for n in verts.values())
weights={frozenset(z) for z in r['chain_audit']['explicit_cocycle_edges']}
assert weights <= set(e)
assert len(weights)==12
for tri in f:
 assert sum(frozenset(ed) in weights for ed in itertools.combinations(tri,2))%2==0
assert sum(ed in weights for ed in C)%2==1
# Independent matrix rank computation of d2.
EI={frozenset(ed):i for i,ed in enumerate(sorted([tuple(sorted(q)) for q in e]))}
pivots={}
for tri in f:
 vec=sum(1<<EI[frozenset(ed)] for ed in itertools.combinations(tri,2))
 while vec:
  bit=(vec&-vec).bit_length()-1
  if bit not in pivots:pivots[bit]=vec;break
  vec^=pivots[bit]
assert len(pivots)==r['chain_audit']['rank_d2']==51
assert len(e)==67 and len(f)==102 and len(T)==51
print(json.dumps({'status':'COMPUTATION_PASS','replayed_moves':len(r['moves']),'final_tetrahedra':len(T),'faces':len(f),'edges':len(e),'mod2_cocycle_edges':len(weights),'rank_d2_independent':len(pivots),'verified_witness':True,'verified_nonboundary_cocycle':True,'input_sha256':hashlib.sha256(P.read_bytes()).hexdigest()},indent=2))