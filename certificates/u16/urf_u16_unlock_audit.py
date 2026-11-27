#!/usr/bin/env python3
"""Pure Python exact finite audit of first old-old 3->2 unlock after one 1->4.
Source: Bagchi-Datta's seven cyclic generators of Dougherty-Faber-Murphy U(16).
No mathematical theorem prover is run. No dependencies or downloads.
"""
from collections import Counter, defaultdict
from itertools import combinations
import hashlib, json, sys
BASES=((0,1,4,6),(0,1,4,9),(0,1,6,14),(0,1,8,9),(0,1,8,10),(0,1,10,14),(0,2,9,13))
N=16
canon=lambda t: tuple(sorted(t))
ORIGINAL=frozenset(canon((v+k)%N for v in base) for base in BASES for k in range(N))

def incidence(T):
    faces=defaultdict(list); edges=defaultdict(list); vertices=defaultdict(list)
    for t in T:
        for f in combinations(t,3): faces[f].append(t)
        for e in combinations(t,2): edges[e].append(t)
        for v in t: vertices[v].append(t)
    return faces,edges,vertices

def legal_sites(T):
    faces,edges,vertices=incidence(T)
    m23=[];m32=[];m41=[]
    for f,ts in faces.items():
        if len(ts)!=2: continue
        d=next(iter(set(ts[0])-set(f))); e=next(iter(set(ts[1])-set(f)))
        if d!=e and canon((d,e)) not in edges:m23.append((f,d,e))
    for edge,ts in edges.items():
        if len(ts)!=3:continue
        pairs=[canon(set(t)-set(edge)) for t in ts]
        tri=canon(set().union(*(set(p) for p in pairs)))
        if len(tri)==3 and len(set(pairs))==3 and set(pairs)==set(combinations(tri,2)) and tri not in faces:
            m32.append((edge,tri))
    for v,ts in vertices.items():
        if len(ts)!=4:continue
        outer=canon(set().union(*(set(t)-{v} for t in ts)))
        if len(outer)!=4 or outer in T:continue
        required={canon((*p,v)) for p in combinations(outer,3)}
        if required==set(ts):m41.append((v,outer))
    return sorted(m23),sorted(m32),sorted(m41)

def flip23(T,m):
    f,d,e=m; old={canon((*f,d)),canon((*f,e))}
    new={canon((*p,d,e)) for p in combinations(f,2)}
    assert len(old)==2 and len(new)==3 and old<=T and not (new&T)
    return frozenset((set(T)-old)|new)

def flip32(T,m):
    edge,tri=m
    old={canon((*p,*edge)) for p in combinations(tri,2)}
    new={canon((*tri,v)) for v in edge}
    assert len(old)==3 and len(new)==2 and old<=T and not(new&T)
    return frozenset((set(T)-old)|new)

def stabilize(t):
    return frozenset((set(ORIGINAL)-{t})|{canon((*p,16)) for p in combinations(t,3)})

def closed_links(T):
    faces,_,vertices=incidence(T)
    if not all(len(ts)==2 for ts in faces.values()):return False
    for v,star in vertices.items():
        triangles=[canon(set(t)-{v}) for t in star]
        vs=set().union(*(set(t) for t in triangles))
        es={e for tri in triangles for e in combinations(tri,2)}
        if len(vs)-len(es)+len(triangles)!=2:return False
        neighbors=defaultdict(set)
        for i,tri in enumerate(triangles):
            for e in combinations(tri,2):neighbors[e].add(i)
        adj=defaultdict(set)
        for inds in neighbors.values():
            for i in inds: adj[i].update(inds)
        seen={0}; todo=[0]
        while todo:
            for j in adj[todo.pop()]-seen:seen.add(j);todo.append(j)
        if len(seen)!=len(triangles):return False
    return True

def first_unlock(t,maxdepth=3):
    S=stabilize(t)
    frontier=[(S,())]; seen={S}; enumerated=0
    for depth in range(maxdepth+1):
        nexts=[]
        for W,path in frontier:
            enumerated+=1
            p23,p32,_=legal_sites(W)
            candidates=[site for site in p32 if 16 not in site[0]]
            if candidates:return depth,path,candidates[0],W,enumerated
            if depth==maxdepth:continue
            for kind,steps,flip in [('23',p23,flip23),('32',p32,flip32)]:
                for site in steps:
                    U=flip(W,site)
                    if U not in seen:
                        seen.add(U);nexts.append((U,path+((kind,site),)))
        frontier=nexts
    return None

def audit():
    assert len(ORIGINAL)==104 and closed_links(ORIGINAL)
    assert len(incidence(ORIGINAL)[1])==120
    assert tuple(len(x) for x in legal_sites(ORIGINAL))==(0,0,0)
    depthcounts=Counter(); reps={}; nodes=0; checks=0
    for t in sorted(ORIGINAL):
        S=stabilize(t)
        assert len(S)==107 and closed_links(S)
        a,b,c=legal_sites(S)
        assert (len(a),len(b),len(c))==(4,0,1) and c[0][0]==16
        out=first_unlock(t)
        assert out is not None
        depth,path,unlock,W,n=out
        nodes+=n; depthcounts[depth]+=1
        X=S
        for kind,m in path:
            p23,p32,_=legal_sites(X)
            assert m in (p23 if kind=='23' else p32)
            X=flip23(X,m) if kind=='23' else flip32(X,m)
            assert closed_links(X)
            checks+=1
        assert X==W and unlock in legal_sites(X)[1]
        assert 16 not in unlock[0]
        Y=flip32(X,unlock)
        assert closed_links(Y) and unlock[0] not in incidence(Y)[1]
        assert len(Y)==104+3+len([k for k,_ in path if k=='23'])-len([k for k,_ in path if k=='32'])-1
        checks+=1
        if depth not in reps:
            reps[depth]={'stellar_tetrahedron':t,'pre_unlock_moves':path,'unlock_32':unlock,'final_tetrahedra':len(Y), 'phi_final':4*(len(Y)-17)}
    digest=hashlib.sha256('\n'.join(' '.join(map(str,t)) for t in sorted(ORIGINAL)).encode()).hexdigest()
    return {'source':'Dougherty-Faber-Murphy U16, seven cyclic facet generators, modulo 16',
            'original_facets':len(ORIGINAL),'facet_sha256':digest,
            'stabilizations_checked':len(ORIGINAL),'stabilized_23_sites_each':4,
            'stabilized_32_sites_each':0,'stabilized_41_sites_each':1,
            'first_old_old_32_depth_counts':dict(sorted(depthcounts.items())),
            'bfs_states_processed':nodes,'post_stabilization_moves_rechecked':checks,
            'all_witness_intermediates_closed_face_and_connected_sphere_links':True,
            'example_certificates':reps,'status':'COMPUTATION_PASS; NOT_LEAN_VERIFIED; finite U16 only'}

if __name__=='__main__':
    result=audit(); print(json.dumps(result,indent=2,sort_keys=True));
