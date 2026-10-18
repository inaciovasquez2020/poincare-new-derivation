#!/usr/bin/env python3
"""Independent verifier for ../artifacts/incidence-three-counterexample-v1.json."""
from collections import Counter, deque
from itertools import combinations
import json
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "artifacts" / "incidence-three-counterexample-v1.json"

def canon(xs):
    return tuple(sorted(xs))

def faces(t):
    return [canon(f) for f in combinations(t, 3)]

def edges(t):
    return [canon(e) for e in combinations(t, 2)]

def connected(nodes, adjacent):
    if not nodes:
        return True
    seen, todo = {nodes[0]}, deque([nodes[0]])
    while todo:
        cur = todo.popleft()
        for nxt in adjacent(cur):
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return len(seen) == len(nodes)

def main():
    dta = json.loads(DATA.read_text())
    tets = [canon(t) for t in dta["triangulation_tetrahedra"]]
    site = dta["move32_site"]
    a,b,c,d,e = (site[k] for k in ("a","b","c","d","e"))
    x,y = (dta["obstruction"]["opposite_vertices"][k] for k in ("x","y"))

    assert len(tets) == len(set(tets)), "duplicate tetrahedron sets"
    assert all(len(t)==4 and len(set(t))==4 for t in tets), "degenerate tetrahedron"
    fcount = Counter(f for t in tets for f in faces(t))
    assert all(n==2 for n in fcount.values()), "ClosedTriangulationCore face condition fails"

    degree = Counter(v for t in tets for v in t)
    support = set(degree)
    assert all(degree[v] != 4 for v in support), "supported degree-four vertex"

    # TetrahedronVertexOverlapConnected: tetrahedra joined by any shared vertex.
    assert connected(tets, lambda t: [u for u in tets if u != t and set(t)&set(u)]), "tetrahedron overlap disconnected"

    # VertexLinkConnected: link triangles joined by shared link edges.
    for v in support:
        links = [canon(set(t)-{v}) for t in tets if v in t]
        assert connected(links, lambda q: [r for r in links if r != q and len(set(q)&set(r)) == 2]), f"link disconnected at {v}"

    tset = set(tets)
    targets = [canon((a,b,d,e)), canon((a,c,d,e)), canon((b,c,d,e))]
    assert len({a,b,c,d,e}) == 5 and all(t in tset for t in targets), "Move32 site not realized"
    de = sum(d in t and e in t for t in tets)
    assert de == 3, "de incidence != 3"

    face = {a,b,c}
    obs = [t for t in tets if face.issubset(t)]
    assert len(obs)==2, "abc obstruction does not have exactly two tetrahedra"
    opposites = {next(v for v in t if v not in face) for t in obs}
    assert opposites == {x,y} and x != y, "obstruction opposite vertices mismatch"
    assert len({a,b,c,d,e,x,y}) == 7, "obstruction/site vertices not distinct"
    xy = sum(x in t and y in t for t in tets)
    assert xy > 0 and not ((x==d and y==e) or (x==e and y==d)), "complement edge missing or self"
    inc = { "a_x":sum(a in t and x in t for t in tets),
            "b_x":sum(b in t and x in t for t in tets),
            "c_x":sum(c in t and x in t for t in tets) }
    assert inc == dta["edge_incidences_at_x"], "incidence receipt mismatch"
    assert all(n > 3 for n in inc.values()), "disjunction not falsified"
    assert dict(sorted(degree.items())) == {int(k):v for k,v in dta["vertex_degrees"].items()}, "degree receipt mismatch"

    print(json.dumps({
      "status":"PASS",
      "tetrahedra":len(tets),
      "vertex_degrees":dict(sorted(degree.items())),
      "de_incidence":de,
      "obstruction_face":sorted(face),
      "opposite_vertices":sorted((x,y)),
      "xy_incidence":xy,
      "edge_incidences_at_x":inc,
      "closed_core":True,
      "all_vertex_links_connected":True,
      "tetrahedron_vertex_overlap_connected":True,
      "no_degree_four":True,
      "move32_site_realized":True,
      "nonself_complement_edge":True
    }, indent=2))

if __name__ == "__main__":
    main()
