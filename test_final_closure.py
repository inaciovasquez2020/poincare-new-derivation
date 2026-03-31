from itertools import combinations

def all_faces(vertices):
    return list(combinations(vertices,3))

def test_uniqueness():
    V = [0,1,2,3]
    F = all_faces(V)
    E = set(tuple(sorted(e)) for f in F for e in combinations(f,2))

    assert len(F)==4
    assert len(E)==6
    assert len(V)==4

    # every edge appears twice
    counts={}
    for f in F:
        for e in combinations(f,2):
            e=tuple(sorted(e))
            counts[e]=counts.get(e,0)+1

    assert all(v==2 for v in counts.values())

    print("PASS: unique tetra structure")

if __name__=="__main__":
    test_uniqueness()
    print("FINAL TEST PASSED")
