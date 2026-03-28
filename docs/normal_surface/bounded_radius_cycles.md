# Bounded-Radius Fundamental Cycles in Bounded-Degree Dual Graphs

## Statement (Minimal Missing Lemma)

There exists a constant R = O(1) such that for any graph G* with deg(G*) ≤ Δ,
one can choose a spanning tree T* so that for every non-tree edge e = (u,v),
the fundamental cycle

    c_e = e ∪ path_{T*}(u,v)

satisfies

    diam(c_e) ≤ R.

Moreover, there exists a subset E' of non-tree edges with |E'| = Ω(t)
such that the cycles {c_e : e ∈ E'} are pairwise edge-disjoint.

## Consequences

1. Local support:
   Each γ(c_e) is supported in a bounded-radius neighborhood.

2. Independence:
   Edge-disjoint supports imply linear independence of {γ(c_e)}.

3. Rank lower bound:
   rank(A) ≥ c·t.

4. Local moves:
   Each c_e induces a bounded-support pivot move.

