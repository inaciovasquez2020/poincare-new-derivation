import itertools
import hashlib
import time
import json
import sys

from collections import Counter

pc = getattr(int, "bit_count",
             lambda x: bin(x).count("1"))

print("PYTHON_COMPATIBILITY := PASS")
print("NATIVE_BIT_COUNT :=",
      hasattr(int, "bit_count"))

C = itertools.combinations
CAP = 368
N = 28
MAX_STATES = 50000
SECONDS = 600

T = sorted(C(range(N),4),
           key=lambda t:t[::-1])

bit = {t:1<<i for i,t in enumerate(T)}

M = {k:{s:0 for s in C(range(N),k)}
     for k in (1,2,3)}

for t,b in bit.items():
    for k in M:
        for s in C(t,k):
            M[k][s] |= b

BASES = (
    (0,1,4,6),(0,1,4,9),(0,1,6,14),
    (0,1,8,9),(0,1,8,10),(0,1,10,14),
    (0,2,9,13)
)

original = {
    tuple(sorted((v+j)%16 for v in t))
    for t in BASES for j in range(16)
}

digest = hashlib.sha256(
    "\n".join(" ".join(map(str,t))
              for t in sorted(original)).encode()
).hexdigest()

assert digest == (
    "4e4e4e280195ff124ceb19c5ca0934a3f"
    "5829b94ed9a45ca25537d89bf907ccb"
)

O = sum(bit[t] for t in original)

def decode(x):
    while x:
        b = x & -x
        yield T[b.bit_length()-1]
        x ^= b

def mask(ts):
    return sum(bit[tuple(sorted(t))]
               for t in ts)

def vertices(x):
    return [v for (v,),m in M[1].items()
            if x&m]

def phi(x):
    return sum(abs(pc(x&m)-4)
               for m in M[1].values()
               if x&m)

def moves(x,d):
    V = vertices(x)

    if d+8 <= CAP:
        fresh = next(
            (v for v in range(N)
             if not x&M[1][(v,)]),None
        )

        if fresh is not None:
            for t in decode(x):
                yield (
                    (x^bit[t]) |
                    mask((*f,fresh)
                         for f in C(t,3)),
                    (t,(fresh,))
                )

    for k in (1,2,3):
        if k==3 and d+4>CAP:
            continue

        for a in C(V,k):
            old = x&M[k][a]

            if pc(old)!=5-k:
                continue

            A = set(a)
            B = set().union(
                *map(set,decode(old))
            )-A

            if len(B)!=5-k:
                continue

            b = tuple(sorted(B))

            if old!=mask(A|(B-{v}) for v in B):
                continue

            absent = (
                bit[b] if len(b)==4
                else M[len(b)][b]
            )

            if x&absent:
                continue

            yield (
                (x^old)|mask(B|(A-{v}) for v in A),
                (a,b)
            )

assert len(original)==104
assert phi(O)==352

initial_moves = list(moves(O,352))

assert len(initial_moves)==104
assert all(len(a)==4
           for _,(a,b) in initial_moves)

reps = sorted({
    min(tuple(sorted((v+j)%16 for v in t))
        for j in range(16))
    for t in original
})

assert len(reps)==7

assert {
    tuple(sorted((v+j)%16 for v in t))
    for t in reps for j in range(16)
}==original

PREFIX = [
    ((0,1,4,6),(16,)),
    ((0,1,6),(14,16)),
    ((0,4,6),(7,16)),
    ((0,6),(7,14,16)),
    ((2,3,8),(0,6)),
    ((2,8),(0,6,9)),
    ((3,8),(0,6,15))
]

PATH12 = PREFIX + [
    ((3,15),(0,5,6)),
    ((5,15),(0,6,13)),
    ((1,2,7),(5,15)),
    ((1,7),(5,8,15)),
    ((2,7),(5,14,15))
]

PATH13 = PREFIX + [
    ((1,5,7),(2,8)),
    ((1,7),(2,8,15)),
    ((0,4,16),(1,7)),
    ((0,16),(1,7,14)),
    ((4,16),(1,6,7)),
    ((16,),(1,6,7,14))
]

def replay(path,expected_vertices):
    K = {frozenset(t) for t in original}
    defects = []

    for i in range(len(path)+1):
        faces = Counter(
            frozenset(f)
            for t in K for f in C(t,3)
        )

        assert all(n==2
                   for n in faces.values())

        deg = Counter(v for t in K for v in t)
        defects.append(
            sum(abs(n-4) for n in deg.values())
        )

        if i==len(path):
            break

        a,b = map(frozenset,path[i])

        assert a and b and not a&b
        assert len(a|b)==5

        old = {t for t in K if a<=t}

        assert old=={a|(b-{v}) for v in b}
        assert not any(b<=t for t in K)

        K = (K-old)|{b|(a-{v}) for v in a}

    assert max(defects)==368
    assert defects[-1]==348
    assert len(deg)==expected_vertices

    return {
        "moves":len(path),
        "defects":defects,
        "vertices":len(deg),
        "tetrahedra":len(K)
    }

witnesses = [
    replay(PATH12,17),
    replay(PATH13,16)
]

print("WITNESS_REPLAY := PASS")
print(json.dumps(witnesses,indent=2))

def search(limit,restore,expected):
    start = time.monotonic()

    frontier = [
        (O^bit[t]) |
        mask((*f,16) for f in C(t,3))
        for t in reps
    ]

    seen = set(frontier)
    expanded = 0
    layers = []

    def target(x,d):
        return d<352 and (
            not restore or len(vertices(x))==16
        )

    def guard():
        if (
            len(seen)>MAX_STATES or
            time.monotonic()-start>SECONDS
        ):
            print("RESOURCE_GUARD := INCOMPLETE")
            sys.exit(2)

    for depth in range(1,limit+1):
        print("DEPTH",depth,
              "FRONTIER",len(frontier),
              "SEEN",len(seen),flush=True)

        layers.append(
            [depth,len(frontier),len(seen)]
        )

        guard()
        nexts = []

        for x in frontier:
            guard()
            expanded += 1
            d = phi(x)

            if target(x,d):
                print("SHORTER_DESCENT_FOUND")
                sys.exit(3)

            if depth==limit:
                continue

            for y,_ in moves(x,d):
                dy = phi(y)

                if dy>CAP:
                    continue

                remaining = limit-depth-1

                if dy-8*remaining>=352:
                    continue

                if y in seen or y==O:
                    continue

                seen.add(y)
                nexts.append(y)
                guard()

                if target(y,dy):
                    print("SHORTER_DESCENT_FOUND")
                    sys.exit(3)

        frontier = nexts

    assert expanded==len(seen)==expected

    result = {
        "status":"EXHAUSTED_DEPTH_BOUND",
        "cap":CAP,
        "depth":limit,
        "restored_vertices":restore,
        "states":len(seen),
        "expanded":expanded,
        "layers":layers,
        "elapsed_seconds":time.monotonic()-start,
        "immediate_touch_pruning":False,
        "consecutive_insertions_allowed":True,
        "facet_sha256":digest
    }

    print(json.dumps(result,indent=2))
    print("COMPUTATION_PASS")

    return result

results = [
    search(11,False,16187),
    search(12,True,23235)
]

with open(sys.argv[1],"w") as f:
    json.dump({
        "searches":results,
        "witnesses":witnesses
    },f,indent=2)

print("GENERAL_MINIMUM_AT_CAP_368 := 12")
print("RESTORED_MINIMUM_AT_CAP_368 := 13")
print("GATE_13 := PASS")
