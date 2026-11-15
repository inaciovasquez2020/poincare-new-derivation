#!/usr/bin/env python3
"""Deterministic exact witness on a product S2 x S1 triangulation.

Finite counterexample to *unrestricted* local reentry exclusion; NOT a
counterexample to the simply-connected case. Standard library only.
"""
from __future__ import annotations
from itertools import combinations
from collections import defaultdict, Counter, deque
from pathlib import Path
import random, json, hashlib, time

SEED=90612

def product_s2_s1(m=4):
    out=set()
    for i in range(m):
        j=(i+1)%m
        for a,b,c in combinations(range(4),3):
            L=[a*m+i,b*m+i,c*m+i]
            U=[a*m+j,b*m+j,c*m+j]
            for k in range(3):out.add(tuple(sorted(L[:k+1]+U[k:])))
    return out

def index(T):
    faces=defaultdict(list); edges=defaultdict(list)
    for t in sorted(T):
        for f in combinations(t,3):faces[f].append(t)
        for e in combinations(t,2):edges[e].append(t)
    return faces,edges

def legal_moves(T):
    F,E=index(T);opts=[]
    for f,ts in F.items():
        if len(ts)!=2:raise AssertionError('bad face incidence')
        x,y=[next(iter(set(t)-set(f))) for t in ts]
        if x==y:raise AssertionError('two faces same apex')
        if tuple(sorted((x,y))) not in E:
            a,b,c=f
            new={tuple(sorted(z)) for z in [(a,b,x,y),(a,c,x,y),(b,c,x,y)]}
            if len(new)==3 and not (new&T):opts.append((23,f,tuple(sorted((x,y))),tuple(sorted(new)),tuple(ts)))
    for (d,e),ts in E.items():
        if len(ts)!=3:continue
        L=set().union(*(set(t)-{d,e} for t in ts))
        if len(L)!=3:continue
        a,b,c=sorted(L)
        expected={tuple(sorted(z)) for z in [(a,b,d,e),(a,c,d,e),(b,c,d,e)]}
        if set(ts)!=expected:continue
        if (a,b,c) not in F:
            new={tuple(sorted(z)) for z in [(a,b,c,d),(a,b,c,e)]}
            if not(new&T):opts.append((32,(a,b,c),(d,e),tuple(sorted(new)),tuple(ts)))
    return opts

def reentries(T):
    F,E=index(T);out=[]
    for (d,e),ts in sorted(E.items()):
        if len(ts)!=3:continue
        L=set().union(*(set(t)-{d,e} for t in ts))
        if len(L)!=3:continue
        a,b,c=sorted(L)
        if set(ts)!={tuple(sorted(z)) for z in [(a,b,d,e),(a,c,d,e),(b,c,d,e)]}:continue
        if (a,b,c) not in F:continue
        x,y=[next(iter(set(t)-{a,b,c})) for t in F[a,b,c]]
        if x==y or {x,y}=={d,e}:continue
        xy=tuple(sorted((x,y)))
        if len(E.get(xy,()))!=3:continue
        L2=set().union(*(set(t)-set(xy) for t in E[xy]))
        if len(L2)!=3:continue
        if set(E[xy])!={tuple(sorted((p,q,*xy))) for p,q in combinations(sorted(L2),2)}:continue
        if tuple(sorted(L2)) not in F:continue
        out.append(dict(old_edge=[d,e],old_face=[a,b,c],source_tets=sorted(ts),obstructing_face_tets=sorted(F[a,b,c]),complement_vertices=[x,y],new_edge=list(xy),new_link=sorted(L2),new_tets=sorted(E[xy]),new_obstructing_face_tets=sorted(F[tuple(sorted(L2))])))
    return out

def rank_basis(cols):
    basis={}
    for value in cols:
        x=value
        while x:
            k=x.bit_length()-1
            if k not in basis:basis[k]=x;break
            x^=basis[k]
    return basis

def solve_equations(rows,n):
    """Rows are (coeff bit mask, RHS). Return one exact bit solution or None."""
    basis={}
    for coeff,rhs in rows:
        row=coeff|(rhs<<n)
        while (row&((1<<n)-1)):
            k=(row&((1<<n)-1)).bit_length()-1
            if k not in basis:basis[k]=row;break
            row^=basis[k]
        else:
            if (row>>n)&1:return None
    sol=0
    for k,row in sorted(basis.items()):
        rhs=(row>>n)&1
        coeff=(row&((1<<n)-1))^(1<<k)
        if ((coeff&sol).bit_count()&1)!=rhs:sol|=1<<k
    if any(((c&sol).bit_count()&1)!=v for c,v in rows):raise AssertionError('bad solution')
    return sol

def audit(T,C):
    F,E=index(T)
    assert all(len(t)==4 and len(set(t))==4 for t in T)
    assert all(len(ts)==2 for ts in F.values())
    verts=sorted({v for t in T for v in t})
    assert len(verts)==16
    # Vertex links: connected, all link edges in exactly two triangles, Euler 2.
    links=[]
    for v in verts:
        triangles={tuple(x for x in t if x!=v) for t in T if v in t}
        edges_l={e for tri in triangles for e in combinations(tri,2)}
        vertices_l={q for tri in triangles for q in tri}
        incidence=Counter(e for tri in triangles for e in combinations(tri,2))
        assert all(x==2 for x in incidence.values())
        assert len(vertices_l)-len(edges_l)+len(triangles)==2
        seen={next(iter(vertices_l))};queue=list(seen)
        while queue:
            p=queue.pop()
            for z in vertices_l:
                if tuple(sorted((p,z))) in edges_l and z not in seen:
                    seen.add(z);queue.append(z)
        assert seen==vertices_l
        links.append([v,len(vertices_l),len(edges_l),len(triangles)])
    edges=sorted(E);triangles=sorted(F)
    ei={e:i for i,e in enumerate(edges)}
    d2=[sum(1<<ei[e] for e in combinations(f,2)) for f in triangles]
    d1=[sum(1<<verts.index(v) for v in e) for e in edges]
    rankd2=len(rank_basis(d2));rankd1=len(rank_basis(d1))
    cc=0
    for e in C:
        assert e in E
        cc^=1<<ei[e]
    c_boundary=0
    for e in C:
        c_boundary^=d1[ei[e]]
    assert c_boundary==0
    assert not is_span(cc,rank_basis(d2))
    constraints=[(column,0) for column in d2]+[(cc,1)]
    w=solve_equations(constraints,len(edges))
    assert w is not None
    supp=[list(e) for i,e in enumerate(edges) if (w>>i)&1]
    assert all(sum(int(tuple(e) in map(tuple,supp)) for e in combinations(f,2))%2==0 for f in triangles)
    assert sum(int(tuple(e) in map(tuple,supp)) for e in C)%2==1
    return dict(n_vertices=len(verts),n_tetrahedra=len(T),n_edges=len(edges),n_triangles=len(triangles),euler=len(verts)-len(edges)+len(triangles)-len(T),vertex_link_f_vectors=links,rank_d1=rankd1,rank_d2=rankd2,h1_f2_dimension=len(edges)-rankd1-rankd2,three_edge_cycle=[list(e) for e in C],cycle_closed=True,cycle_nonbounding=True,explicit_cocycle_edges=supp,cocycle_triangle_parity_verified=True,cocycle_on_cycle=1)

def is_span(x,basis):
    while x:
        k=x.bit_length()-1
        if k not in basis:return False
        x^=basis[k]
    return True

def run():
    r=random.Random(SEED)
    T=product_s2_s1(4);trace=[]
    assert len(T)==48
    for step in range(400):
        W=reentries(T)
        if W:
            witness=W[0]
            x,y=witness['complement_vertices'];a=witness['old_face'][0]
            C=[tuple(sorted(e)) for e in [(x,a),(a,y),(y,x)]]
            mat=audit(T,C)
            assert mat['h1_f2_dimension']==1
            assert len(trace)==115 and len(T)==51,(len(trace),len(T))
            manifest={'status':'COMPUTATION_PASS','claim':'genuine witnessed reentry in nonsimply-connected S2xS1 triangulation; 3-edge cycle nonbounding','topology':'constructed as simplicial triangulation of boundary tetrahedron cross simplicial circle, then bistellar flips; not simply connected', 'seed':SEED,'number_of_pachner_moves':len(trace),'moves':trace,'witness':witness,'chain_audit':mat,'final_tetrahedra':[list(t) for t in sorted(T)],'scope':'finite explicit instance; universal simply-connected exclusion remains OPEN; Lean NOT_RUN'}
            return manifest
        options=legal_moves(T)
        possible=[o for o in options if (o[0]==23 and len(T)<100) or o[0]==32]
        lowers=[o for o in possible if o[0]==32]
        if not possible:raise AssertionError('stalled')
        o=r.choice(lowers if lowers and r.random()<0.47 else possible)
        move,face,edge,new,old=o
        U=(T-set(old))|set(new)
        FF,EE=index(U)
        assert all(len(z)==2 for z in FF.values())
        trace.append({'move':move,'face':list(face),'edge':list(edge),'removed':[list(t) for t in old],'added':[list(t) for t in new]})
        T=U
    raise AssertionError('witness not found within 400 moves')

if __name__=='__main__':
    result=run()
    p=Path(__file__).with_name('poincare_reentry_adversarial_receipt.json')
    p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','number_of_pachner_moves','witness','chain_audit']},indent=2))
    print('RECEIPT',p)
