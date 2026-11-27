"""Exact F2 obstruction correspondence; uses fixture definitions from prior verifier.
Python stdlib only. Basis checks prove identities for linear forward map on fixtures.
Reverse uses chosen local potentials (not assumed linear); tests sampled cycles.
"""
import contextlib, io, json, runpy
from pathlib import Path
from itertools import combinations
from collections import defaultdict
with contextlib.redirect_stdout(io.StringIO()):
    m = runpy.run_path(str(Path(__file__).with_name('verify_g2_local_potential_gluing.py')))
incidences, kernel, potentials, connected, stellar = (m[k] for k in ('incidences','kernel','potentials','connected','stellar'))
def rank(xs):
    p={}
    for x in xs:
        while x:
            k=x.bit_length()-1
            if k in p: x^=p[k]
            else: p[k]=x;break
    return len(p)
def bit(x,i): return (x>>i)&1
def run(name,tets,full):
    T,F,E,V=incidences(tets); fs=sorted(F); es=sorted(E); fi={f:i for i,f in enumerate(fs)}; ei={e:i for i,e in enumerate(es)}
    frows=[sum(1<<ei[e] for e in combinations(f,2)) for f in fs]
    erows=[sum(1<<fi[f] for f in fs if set(e)<=set(f)) for e in es]
    z1=kernel(frows,len(es)); z2=kernel(erows,len(fs))
    b1=[sum(1<<ei[e] for e in es if v in e) for v in V]
    b2=[sum(1<<fi[f] for f in fs if t in F[f]) for t in range(len(T))]
    assert all(connected(ts,[F[f] for f in fs if v in f]) for v,ts in V.items())
    assert all(connected(ts,[F[f] for f in fs if set(e)<=set(f)]) for e,ts in E.items())
    def value(w,u,v): return 0 if u==v else bit(w,ei[tuple(sorted((u,v)))])
    def forward(w,refs):
        out=0
        for f,(t,t1) in F.items():
            q={value(w,v,refs[t])^value(w,v,refs[t1]) for v in f};assert len(q)==1
            out|=q.pop()<<fi[f]
        assert all((r&out).bit_count()%2==0 for r in erows)
        return out
    def delta3(a):return sum((a[t]^a[t1])<<fi[f] for f,(t,t1) in F.items())
    def delta0(a):return sum((a[u]^a[v])<<ei[u,v] for u,v in es)
    def reverse(s):
        b={v:potentials(ts,[(t,t1,bit(s,fi[f])) for f,(t,t1) in F.items() if v in f]) for v,ts in V.items()}
        if any(x is None for x in b.values()): return None
        w=0
        for e,ts in E.items():
            u,v=e;q={b[u][t]^b[v][t] for t in ts};assert len(q)==1;w|=q.pop()<<ei[e]
        assert all((r&w).bit_count()%2==0 for r in frows)
        return w,b
    refs=[t[0] for t in T]; refs2=[t[-1] for t in T]
    images=[]; forward_checks=0
    for w in z1+[0]:
        s=forward(w,refs);images.append(s)
        assert s^forward(w,refs2)==delta3([value(w,u,v) for u,v in zip(refs,refs2)])
        wr,b=reverse(s)
        a={v:b[v][ts[0]]^value(w,v,refs[ts[0]]) for v,ts in V.items()}
        assert wr^w==delta0(a)
        forward_checks+=1
    for v,w in zip(V,b1):
        assert forward(w,refs)==delta3([int(r==v) for r in refs])
    samples=[0]
    if full:
        assert len(z2)<=16
        for z in z2:samples += [s^z for s in samples]
    else:samples+=z2
    reverse_checks=local_blocked=0
    for s in samples:
        r=reverse(s)
        if r is None:local_blocked+=1;continue
        w,b=r
        assert s^forward(w,refs)==delta3([b[v][t] for t,v in enumerate(refs)])
        reverse_checks+=1
    h1=len(z1)-rank(b1);h2=len(z2)-rank(b2);im=rank(b2+images)-rank(b2)
    assert im==h1
    return dict(name=name,h1=h1,h2=h2,image_dimension=im,locally_solvable_quotient_dimension=im,residual_local_obstruction_dimension=h2-im,forward_basis_checks=forward_checks,reverse_checks=reverse_checks,local_blocked=local_blocked,reverse_mode='exhaustive' if full else 'zero_and_basis')
S=list(combinations(range(5),4));out=[]
for i in range(3):out.append(run('S3_stellar_'+str(i),S,True));S=stellar(S)
out.append(run('S2_times_S1',m['P'],False))
out.append(run('suspension_torus',[f+(v,) for f in m['tri'] for v in [9,10]],False))
print(json.dumps(dict(status='COMPUTATION_PASS',results=out),indent=2))
