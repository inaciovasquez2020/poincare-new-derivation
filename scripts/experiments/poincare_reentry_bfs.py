import random, itertools, collections, json, time, argparse
R=random.Random(20261115)
def faces(t):return [tuple(x for x in t if x!=v) for v in t]
def edges(t):return list(itertools.combinations(t,2))
def idx(T):
 f=collections.defaultdict(list);e=collections.defaultdict(list)
 for t in T:
  for q in faces(t):f[q].append(t)
  for q in edges(t):e[q].append(t)
 return f,e

def candidates(T):
 F,E=idx(T); opts=[]
 for f,tt in F.items():
  if len(tt)!=2:raise ValueError('nonmanifold face')
  x,y=tuple(set(tt[0])-set(f))[0],tuple(set(tt[1])-set(f))[0]
  if x==y:continue
  if tuple(sorted((x,y))) not in E:
   a,b,c=f
   new={tuple(sorted(z)) for z in [(a,b,x,y),(a,c,x,y),(b,c,x,y)]}
   if len(new)==3 and not (new&T):opts.append((23, f, tuple(sorted((x,y))),tuple(sorted(new)),tuple(tt)))
 for (d,e),tt in E.items():
  if len(tt)!=3:continue
  link=set().union(*(set(t)-{d,e} for t in tt))
  if len(link)!=3:continue
  a,b,c=sorted(link)
  expected={tuple(sorted(z)) for z in [(a,b,d,e),(a,c,d,e),(b,c,d,e)]}
  if set(tt)!=expected:continue
  if (a,b,c) not in F:
   new={tuple(sorted(z)) for z in [(a,b,c,d),(a,b,c,e)]}
   if not(new&T):opts.append((32,(a,b,c),(d,e),tuple(sorted(new)),tuple(tt)))
 return opts,F,E

def check(T,F,E):
 witnesses=[]
 for (d,e),tt in E.items():
  if len(tt)!=3:continue
  link=set().union(*(set(t)-{d,e} for t in tt))
  if len(link)!=3:continue
  a,b,c=sorted(link)
  expected={tuple(sorted(z)) for z in [(a,b,d,e),(a,c,d,e),(b,c,d,e)]}
  if set(tt)!=expected:continue
  if (a,b,c) not in F:continue
  # old face obstruction, x and y vertices of the two incident tets
  abct=F[a,b,c]
  if len(abct)!=2:continue
  x=next(iter(set(abct[0])-{a,b,c}));y=next(iter(set(abct[1])-{a,b,c}))
  if x==y or {x,y}=={d,e}:continue
  xy=tuple(sorted((x,y)))
  if len(E.get(xy,[]))==3:
   # next edge has 3 tets, and has a different obstructed triangle itself?
   L=set().union(*(set(t)-set(xy) for t in E[xy]))
   full=(len(L)==3 and set(E[xy])=={tuple(sorted((i,j,*xy))) for i,j in itertools.combinations(L,2)})
   if full:
    L=tuple(sorted(L)); obstruct=L in F
    witnesses.append({'old_edge':[d,e],'old_face':[a,b,c],'face_tets':abct,'complement_edge':[x,y],'new_incidence':3,'new_opposite_face':L,'new_obstructed':obstruct,'next_edge_tets':E[xy]})
 return witnesses

def perm1_4(T):
 t=R.choice(tuple(T));v=max(max(x) for x in T)+1
 return T-{t}|{tuple(sorted(set(t)-{a}|{v})) for a in t},('14',t,v)

start={tuple(sorted(t)) for t in itertools.combinations(range(5),4)}


def subdivide(T, t, v):
 return frozenset((set(T)-{t}) | {tuple(sorted((set(t)-{a})|{v})) for a in t})

def seeds(n):
 current=[frozenset(start)]
 for v in range(5,n):
  current=list({subdivide(T,t,v) for T in current for t in T})
 return current

def audit(T):
 f,e=idx(T)
 if not all(len(ts)==2 for ts in f.values()): raise AssertionError('nonclosed triangular incidence')
 if not all(len(t)==4 and len(set(t))==4 for t in T): raise AssertionError('degenerate tetrahedron')
 return f,e

def bfs(n, max_states, seconds):
 Q=collections.deque(seeds(n)); seen=set(Q);checked=0;steps=0;started=time.monotonic(); witness=None
 while Q and len(seen)<max_states and time.monotonic()-started<seconds:
  T=set(Q.popleft());checked+=1
  F,E=audit(T)
  ws=check(T,F,E)
  if ws:
   witness={'tetrahedra':[list(t) for t in sorted(T)],'reentry':ws}
   break
  opts,_,_=candidates(T)
  for k,f,e,new,old in opts:
   U=frozenset((T-set(old))|set(new));steps+=1
   if U not in seen: seen.add(U);Q.append(U)
 result={'vertices':n,'seed':'boundary of 4-simplex, then all labeled stellar subdivisions to vertex count',
         'checked_states':checked,'discovered_states':len(seen),'directed_moves_checked':steps,
         'remaining_queue':len(Q),'status':'WITNESS' if witness else ('COMPLETE_NO_WITNESS' if not Q else 'INCOMPLETE'),
         'max_states':max_states,'seconds_limit':seconds, 'witness':witness}
 return result

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--vertices',type=int,choices=(6,7,8),required=True)
 ap.add_argument('--max-states',type=int,default=150000);ap.add_argument('--seconds',type=float,default=18)
 ap.add_argument('--output',type=str,default=None)
 a=ap.parse_args();result=bfs(a.vertices,a.max_states,a.seconds)
 print(json.dumps(result,indent=2,default=list))
 if a.output:
  with open(a.output,'w') as h:json.dump(result,h,indent=2,default=list)