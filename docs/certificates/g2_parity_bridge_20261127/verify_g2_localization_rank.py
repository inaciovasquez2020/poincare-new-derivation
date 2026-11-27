"""Independent GF(2) localization-map rank audit (stdlib only).
Uses previous fixture geometry, not its potential solver or kernel/rank algorithms.
Checks all linear basis vectors, including boundary generators; no enumeration of exponential cycle sets.
"""
import contextlib, io, json, runpy, time
from pathlib import Path
from itertools import combinations
from collections import defaultdict
with contextlib.redirect_stdout(io.StringIO()):
    old=runpy.run_path(str(Path(__file__).with_name('verify_g2_local_potential_gluing.py')))

def rref(rows,n):
    a=[r for r in rows if r]; piv=[]; i=0
    for j in range(n):
        k=next((k for k in range(i,len(a)) if a[k]>>j&1),None)
        if k is None:continue
        a[i],a[k]=a[k],a[i]
        for k in range(len(a)):
            if k!=i and a[k]>>j&1:a[k]^=a[i]
        piv.append(j);i+=1
    return a[:i],piv

def ker(rows,n):
    a,p=rref(rows,n);out=[]
    for j in range(n):
        if j in p:continue
        x=1<<j
        for r,k in zip(a,p):
            if r>>j&1:x|=1<<k
        out.append(x)
    assert all((r&x).bit_count()%2==0 for r in rows for x in out)
    return out

def rank(xs,n):return len(rref(xs,n)[1])
def quotient(cols,n):
    a,p=rref(cols,n)
    def reduce(x):
        for r,k in zip(a,p):
            if x>>k&1:x^=r
        return x
    return reduce,len(p)

def connected(nodes,pairs):
    seen={next(iter(nodes))}; todo=list(seen); adj=defaultdict(list)
    for a,b in pairs:adj[a].append(b);adj[b].append(a)
    for a in todo:
        for b in adj[a]:
            if b not in seen:seen.add(b);todo.append(b)
    return seen==set(nodes)

def audit(name,tets):
    T=sorted(set(tuple(sorted(t)) for t in tets)); V=sorted(set().union(*map(set,T)))
    F=sorted({f for t in T for f in combinations(t,3)}); E=sorted({e for t in T for e in combinations(t,2)})
    assert len(T)<=500 and len(F)<=1000 and len(V)<=100
    fi={f:i for i,f in enumerate(F)}; ei={e:i for i,e in enumerate(E)}
    co={f:[i for i,t in enumerate(T) if set(f)<=set(t)] for f in F};assert all(len(x)==2 for x in co.values())
    for q in [(v,) for v in V]+E:
        nodes=[i for i,t in enumerate(T) if set(q)<=set(t)]
        assert connected(nodes,[co[f] for f in F if set(q)<=set(f)])
    d2=[sum(1<<fi[f] for f in F if set(e)<=set(f)) for e in E]
    d3=[sum(1<<fi[f] for f in combinations(t,3)) for t in T]
    z2=ker(d2,len(F)); b2=rank(d3,len(F));assert all((r&c).bit_count()%2==0 for r in d2 for c in d3)
    z1=ker([sum(1<<ei[e] for e in combinations(f,2)) for f in F],len(E))
    b1=rank([sum(1<<ei[e] for e in E if v in e) for v in V],len(E));h1=len(z1)-b1;h2=len(z2)-b2
    link_data=[];offset=0;local_dims=[]
    for v in V:
        lv=sorted({u for e in E if v in e for u in e if u!=v})
        le=sorted({tuple(u for u in f if u!=v) for f in F if v in f})
        lt=sorted({tuple(u for u in t if u!=v) for t in T if v in t})
        li={e:i for i,e in enumerate(le)}
        l1=[sum(1<<li[e] for e in le if u in e) for u in lv]
        l2=[sum(1<<li[e] for e in combinations(t,2)) for t in lt]
        assert all((r&c).bit_count()%2==0 for r in l1 for c in l2)
        red,br=quotient(l2,len(le));dim=len(ker(l1,len(le)))-br
        local_dims.append((v,dim));link_data.append((offset,l1,red,[fi[tuple(sorted((v,)+e))] for e in le]));offset+=len(le)
    def localize(s):
        y=0
        for off,l1,red,indices in link_data:
            x=sum(((s>>j)&1)<<i for i,j in enumerate(indices))
            assert all((r&x).bit_count()%2==0 for r in l1)
            y|=red(x)<<off
        return y
    assert all(localize(s)==0 for s in d3)
    images=[localize(s) for s in z2];rr=rank(images,offset)
    # Compute the kernel directly on coefficients of the global cycle basis.
    rows=[sum(((x>>j)&1)<<i for i,x in enumerate(images)) for j in range(offset)]
    k=ker(rows,len(z2));assert all(localize(__import__('functools').reduce(int.__xor__,(z for i,z in enumerate(z2) if c>>i&1),0))==0 for c in k)
    locquot=len(k)-b2;assert locquot==h1;assert h2==h1+rr
    return dict(name=name,V=len(V),E=len(E),F=len(F),T=len(T),h1=h1,h2=h2,local_target_dimension=sum(d for _,d in local_dims),nonzero_link_h1=[(v,d) for v,d in local_dims if d],localization_rank=rr,locally_solvable_quotient_dimension=locquot,cycle_basis_checks=len(z2),boundary_generator_checks=len(d3),localization_kernel_basis_checks=len(k))

def torus(m,n):
    ix=lambda i,j:(i%m)*n+j%n
    out=[]
    for i in range(m):
        for j in range(n):
            a,b,c,d=ix(i,j),ix(i+1,j),ix(i+1,j+1),ix(i,j+1)
            out.extend([tuple(sorted((a,b,c))),tuple(sorted((a,c,d)))])
    return sorted(set(out))

def connect_sum(a,b):
    a=list(a);b=list(b);f=a.pop(0);g=b.pop(0)
    off=max(max(x) for x in a+[f])+1
    mp=dict(zip(g,f))
    return a+[tuple(sorted(mp.get(v,v+off) for v in t)) for t in b]
def susp(s):
    v=max(map(max,s))+1
    return [f+(u,) for f in s for u in (v,v+1)]
start=time.monotonic();out=[]
S=list(combinations(range(5),4))
for i in range(3):
    out.append(audit('S3_stellar_'+str(i),S));S=old['stellar'](S)
out.append(audit('S2_times_S1',old['P']))
for m,n in [(3,3),(3,4),(4,4)]:out.append(audit(f'suspension_torus_{m}x{n}',susp(torus(m,n))))
out.append(audit('suspension_genus2',susp(connect_sum(torus(3,3),torus(3,3)))))
assert [x['localization_rank'] for x in out]==[0,0,0,0,2,2,2,4]
print(json.dumps(dict(status='COMPUTATION_PASS',method='independent RREF; exact basis checks',fixtures=len(out),cycle_basis_checks=sum(x['cycle_basis_checks'] for x in out),boundary_generator_checks=sum(x['boundary_generator_checks'] for x in out),localization_kernel_basis_checks=sum(x['localization_kernel_basis_checks'] for x in out),elapsed_seconds=round(time.monotonic()-start,4),results=out),indent=2))
