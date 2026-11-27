"""Exact mod-2 local-potential gluing regression. Python 3 stdlib only."""
from itertools import combinations
from collections import defaultdict, deque
import json

def canon(xs): return tuple(sorted(xs))
def incidences(tets):
    T=sorted(set(map(canon,tets)))
    assert all(len(set(t))==4 for t in T)
    F=defaultdict(list); E=defaultdict(list); V=defaultdict(list)
    for i,t in enumerate(T):
        for f in combinations(t,3): F[f].append(i)
        for e in combinations(t,2): E[e].append(i)
        for v in t: V[v].append(i)
    assert all(len(c)==2 for c in F.values())
    return T,F,E,V

def kernel(rows,n):
    piv={}
    for row in rows:
        while row:
            k=row.bit_length()-1
            if k in piv: row^=piv[k]
            else: piv[k]=row;break
    out=[]
    for j in range(n):
        if j in piv: continue
        x=1<<j
        for k,row in sorted(piv.items()):
            if (row&x).bit_count()%2: x^=1<<k
        out.append(x)
    assert len(out)==n-len(piv)
    assert all((r&x).bit_count()%2==0 for r in rows for x in out)
    return out

def potentials(nodes,edges):
    adj=defaultdict(list)
    for u,v,b in edges: adj[u].append((v,b));adj[v].append((u,b))
    a={}
    for root in nodes:
        if root in a: continue
        a[root]=0;q=deque([root])
        while q:
            u=q.popleft()
            for v,b in adj[u]:
                x=a[u]^b
                if v in a:
                    if a[v]!=x:return None
                else:a[v]=x;q.append(v)
    return a

def connected(nodes,edges):
    nodes=set(nodes); todo=list(nodes)[:1];seen=set(todo);adj=defaultdict(list)
    for u,v in edges:adj[u].append(v);adj[v].append(u)
    for u in todo:
        for v in adj[u]:
            if v not in seen:seen.add(v);todo.append(v)
    return seen==nodes

def run(name,tets,exhaustive=False):
    T,F,E,V=incidences(tets); faces=sorted(F); fi={f:i for i,f in enumerate(faces)}
    ef=defaultdict(list)
    for f in faces:
        for e in combinations(f,2):ef[e].append(f)
    rows=[sum(1<<fi[f] for f in ef[e]) for e in E]
    basis=kernel(rows,len(faces)); assert len(basis)<=20 or not exhaustive
    assert connected(range(len(T)),list(F.values()))
    for e,ts in E.items(): assert connected(ts,[F[f] for f in ef[e]])
    byv={v:[f for f in faces if v in f] for v in V}
    link_chi={v:sum(v in e for e in E)-len(byv[v])+len(V[v]) for v in V}
    samples=[0]
    if exhaustive:
        for b in basis:samples += [s^b for s in samples]
    else:samples += basis
    counts=defaultdict(int)
    for s in samples:
        assert all((r&s).bit_count()%2==0 for r in rows)
        val=lambda f:(s>>fi[f])&1
        local={v:potentials(V[v],[(F[f][0],F[f][1],val(f)) for f in byv[v]]) for v in V}
        direct=potentials(range(len(T)),[(a,b,val(f)) for f,(a,b) in F.items()])
        if any(p is None for p in local.values()):
            counts['local_obstruction']+=1;assert direct is None;continue
        w={}
        for (u,v),ts in E.items():
            ds={local[u][t]^local[v][t] for t in ts};assert len(ds)==1;w[u,v]=ds.pop()
        for a,b,c in F:assert w[a,b]^w[b,c]^w[a,c]==0
        A=potentials(V,[(u,v,b) for (u,v),b in w.items()])
        if A is None:
            counts['global_obstruction']+=1;assert direct is None;continue
        B=[]
        for i,t in enumerate(T):
            bs={local[v][i]^A[v] for v in t};assert len(bs)==1;B.append(bs.pop())
        assert all(B[a]^B[b]==val(f) for f,(a,b) in F.items())
        assert direct is not None
        counts['glued']+=1
    return dict(name=name,V=len(V),E=len(E),F=len(F),T=len(T),cycle_dimension=len(basis),link_euler_values=sorted(set(link_chi.values())),mode='exhaustive' if exhaustive else 'zero_and_basis',tested=len(samples),outcomes=dict(counts))

def stellar(T):
    T=list(T);t=T.pop(0);v=max(max(x) for x in T+[t])+1
    return T+[canon(f+(v,)) for f in combinations(t,3)]

S=list(combinations(range(5),4));results=[]
for i in range(3):
    results.append(run('S3_stellar_'+str(i),S,True));S=stellar(S)
# Product of the boundary of a tetrahedron and a 3-edge circle.
P=[]
for a,b,c in combinations(range(4),3):
    for i,j in [(0,1),(1,2),(0,2)]:
        x=lambda u,k:3*u+k
        P += [(x(a,i),x(b,i),x(c,i),x(c,j)),(x(a,i),x(b,i),x(b,j),x(c,j)),(x(a,i),x(a,j),x(b,j),x(c,j))]
results.append(run('S2_times_S1',P))
# Suspension of a periodic 3x3 triangulated torus: simply connected but not a 3-manifold.
tri=[]
idx=lambda i,j:(i%3)*3+j%3
for i in range(3):
    for j in range(3):
        a,b,c,d=idx(i,j),idx(i+1,j),idx(i+1,j+1),idx(i,j+1)
        tri += [(a,b,c),(a,c,d)]
results.append(run('suspension_torus',[f+(v,) for f in tri for v in [9,10]]))
assert all(r['outcomes']=={'glued':r['tested']} for r in results[:3])
assert results[3]['outcomes'].get('global_obstruction',0)>0 and not results[3]['outcomes'].get('local_obstruction',0)
assert results[4]['outcomes'].get('local_obstruction',0)>0
print(json.dumps(dict(status='COMPUTATION_PASS',results=results),indent=2))
