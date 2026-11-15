#!/usr/bin/env python3
"""Read-only finite audit of the witnessed-reentry obstruction.
Uses adjacent poincare_reentry_bfs.py as candidate generator, plus independent
incidence and link audits. Does not claim universal triangulation coverage.
"""
import argparse, collections, hashlib, importlib.util, itertools, json, pathlib, sys, time
ROOT=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('poincare_reentry_bfs',ROOT/'poincare_reentry_bfs.py')
ref=importlib.util.module_from_spec(spec);spec.loader.exec_module(ref)

def independent_index(T):
    faces=collections.defaultdict(set); edges=collections.defaultdict(set)
    for t in T:
        assert tuple(sorted(set(t)))==t and len(t)==4, ('invalid tetrahedron',t)
        for f in itertools.combinations(t,3):faces[f].add(t)
        for e in itertools.combinations(t,2):edges[e].add(t)
    assert all(len(ts)==2 for ts in faces.values()), 'nonclosed face'
    V=set().union(*map(set,T))
    assert len(V)-len(edges)+len(faces)-len(T)==0,'Euler'
    for v in V:
        triangles={tuple(x for x in t if x!=v) for t in T if v in t}
        ledge=collections.Counter(e for tri in triangles for e in itertools.combinations(tri,2))
        assert all(c==2 for c in ledge.values()),('link incidence',v)
        W=set().union(*map(set,triangles))
        assert len(W)-len(ledge)+len(triangles)==2,('link Euler',v)
        neighbors={x:set() for x in W}
        for a,b in ledge:neighbors[a].add(b);neighbors[b].add(a)
        reached=set(); frontier=[next(iter(W))]
        while frontier:
            x=frontier.pop()
            if x not in reached:reached.add(x);frontier.extend(neighbors[x]-reached)
        assert reached==W,('link disconnected',v)
    return faces,edges

def independent_reentry(T,F,E):
    # The old 3-edge star must have exactly three tetrahedra, with its
    # opposite face present. Two tetrahedra on that face give x,y. The new
    # edge xy must have incidence three and its opposite face be obstructed.
    nblocked=nnonself=npresent=nthree=0; witnesses=[]
    for de,star in E.items():
        if len(star)!=3:continue
        L=set().union(*(set(t)-set(de) for t in star))
        if len(L)!=3:continue
        a,b,c=sorted(L);d,e=de
        expected={tuple(sorted((d,e,u,v))) for u,v in itertools.combinations((a,b,c),2)}
        if star!=expected or (a,b,c) not in F:continue
        nblocked+=1
        fts=F[a,b,c]
        if len(fts)!=2:continue
        x,y=sorted([next(iter(set(t)-{a,b,c})) for t in fts])
        if x==y or {x,y}=={d,e}:continue
        nnonself+=1
        xy=(x,y)
        if xy not in E:continue
        npresent+=1
        if len(E[xy])!=3:continue
        nthree+=1
        newlink=set().union(*(set(t)-set(xy) for t in E[xy]))
        if len(newlink)!=3:continue
        needed={tuple(sorted((x,y,u,v))) for u,v in itertools.combinations(sorted(newlink),2)}
        if needed!=E[xy]:continue
        if tuple(sorted(newlink)) in F:
            witnesses.append({'old_edge':de,'old_face':(a,b,c),'new_edge':xy,'new_face':tuple(sorted(newlink)),'tetrahedra':sorted(T)})
    return dict(blocked=nblocked,nonself=nnonself,complement_present=npresent,complement_degree_three=nthree,witnesses=witnesses)

def run(n,max_states,seconds):
    start=time.monotonic()
    seeds=ref.seeds(n); Q=collections.deque(sorted(seeds)); seen=set(Q)
    tally=collections.Counter(); transition_count=0; checked=0; digest=hashlib.sha256(); found=None; limit=None
    if len(seen)>max_states:limit='seed_state_cap'
    while Q and limit is None:
        if checked>=max_states:limit='checked_state_cap';break
        if time.monotonic()-start>=seconds:limit='wall_time_cap';break
        T=Q.popleft();checked+=1
        F,E=independent_index(T)
        indep=independent_reentry(T,F,E)
        tally.update({k:v for k,v in indep.items() if k!='witnesses'})
        F2,E2=ref.idx(set(T))
        original=ref.check(set(T),F2,E2)
        if bool(original)!=bool(indep['witnesses']):
            raise AssertionError(('original versus independent witness disagreement',T,original,indep['witnesses']))
        if indep['witnesses']:
            found=indep['witnesses'][0];break
        digest.update(str(sorted(T)).encode('ascii'))
        moves,_,_=ref.candidates(set(T))
        for typ,face,edge,new,old in moves:
            U=frozenset((set(T)-set(old))|set(new));transition_count+=1
            # Verify exact exchange and preservation of the vertex set.
            assert len(new)==(3 if typ==23 else 2)
            assert len(old)==(2 if typ==23 else 3)
            assert len(U)==len(T)+(1 if typ==23 else -1)
            assert set().union(*map(set,U))==set().union(*map(set,T))
            if U not in seen:
                if len(seen)>=max_states:
                    limit='discovered_state_cap';break
                seen.add(U);Q.append(U)
    status='WITNESS_FOUND' if found else ('COMPLETE_NO_WITNESS' if not Q and limit is None else 'INCOMPLETE')
    return {'vertices':n,'status':status,'checked_states':checked,'discovered_states':len(seen),'directed_moves':transition_count,'remaining_queue':len(Q), 'limits':{'max_states':max_states,'seconds':seconds,'triggered':limit},'counts':dict(tally),'witness':found,'state_stream_sha256':digest.hexdigest(),'elapsed_seconds':round(time.monotonic()-start,3),'scope':'all fixed-vertex labeled 2-3/3-2 states reachable from all iterated 1-4 subdivision seeds of boundary(4-simplex)'}

def self_test():
    T=frozenset(tuple(t) for t in itertools.combinations(range(5),4))
    F,E=independent_index(T)
    assert independent_reentry(T,F,E)['witnesses']==[]
    U=ref.subdivide(T,next(iter(sorted(T))),5)
    independent_index(U)
    # Negative tests must fail before state enumeration.
    for bad in [frozenset(set(T)-{next(iter(sorted(T)))}),frozenset({(0,1,2,2)})]:
        try:independent_index(bad)
        except (AssertionError,ValueError,TypeError):pass
        else:raise AssertionError('failed negative manifold test')
    return 'PASS'

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--vertices',type=int,nargs='+',choices=(6,7,8),default=[6,7]);p.add_argument('--max-states',type=int,default=150000);p.add_argument('--seconds-per-case',type=float,default=30.);p.add_argument('--output',type=pathlib.Path,default=ROOT/'poincare_full_reentry_receipt.json');a=p.parse_args()
    assert a.max_states>0 and a.seconds_per_case>0
    try:
        initial=self_test();cases=[run(n,a.max_states,a.seconds_per_case) for n in a.vertices]
        summary={'self_tests':initial,'python':sys.version.split()[0],'source_files':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ['poincare_full_reentry_test.py','poincare_reentry_bfs.py']},'cases':cases,'global_theorem':'OPEN','lean':'NOT_RUN','pass_condition':'Only individual COMPLETE_NO_WITNESS components count as full finite checks'}
        a.output.write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps(summary,indent=2))
        sys.exit(0 if all(c['status']=='COMPLETE_NO_WITNESS' for c in cases) else 2)
    except Exception as ex:
        print('AUDIT_ERROR:',repr(ex),file=sys.stderr);sys.exit(3)