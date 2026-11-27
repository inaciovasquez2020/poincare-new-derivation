# Explicit obstruction correspondence for the G2 parity bridge

2026-11-27. PROVED_ON_PAPER. Lean candidate for forward gluing only; NOT_RUN. Exact finite tests COMPUTATION_PASS. No novelty claim or global Poincare claim.

## Setting

K is a finite pure simplicial 3-complex with exactly two distinct tetrahedra per triangular face. Assume the tetrahedra containing each represented edge form a connected graph via faces containing that edge, and the tetrahedra containing each represented vertex form a connected graph via faces containing that vertex. These are local connectivity hypotheses, not global H1 or H2 vanishing. Work over F2. For a face f with cofaces t,t', write (dB)(f)=B(t)+B(t'), so d is the actual primal boundary_3. Write Z^1 for symmetric edge cocycles with triangle cancellation, B^1 for vertex coboundaries. Extend edge weights to diagonal zero. Let Z_2^loc be the space of face cycles S admitting vertex-star potentials b_v satisfying b_v(t)+b_v(t')=S(f) whenever v belongs to f. It is a vector space (sum the witnesses). Every tetrahedron boundary is locally solvable (restrict its potential), so B_2=im d is contained in Z_2^loc.

## Theorem

There is an explicit linear isomorphism H^1(K;F2) ~= Z_2^loc/B_2. If all vertex links have H_1=0, then Z_2^loc=Z_2 and the target is H_2(K;F2). This is a chain-level form of the relevant mod-two duality, not a claim of a new duality theorem.

## Forward map (new construction)

Fix a vertex r(t) of every tetrahedron t. For a cocycle w define b_v^w(t)=w(v,r(t)) for v in t. For each face f with two cofaces t,t', set S_w(f)=b_v^w(t)+b_v^w(t') using any v in f.

This is independent of v: for u,v in f, triangle cancellation (including repeated vertices) yields w(u,r(t))+w(v,r(t))=w(u,v) and the same identity in t'. Adding these shows that the two candidate face values agree. The assignment is linear. For any edge e, choose an endpoint v. Sum S_w(f) over all faces containing e, using the same v in each term. Every tetrahedron containing e has exactly two triangular faces containing e, so every b_v^w(t) occurs twice. Hence S_w is a cycle. By construction S_w admits local potentials and belongs to Z_2^loc.

If w=delta A, then S_w=dB with B(t)=A(r(t)); the A(v) terms cancel. Thus w -> S_w descends to H^1 -> Z_2^loc/B_2. Changing references r to r' changes S_w by dC where C(t)=w(r(t),r'(t)), again by triangle cancellation. The induced map is independent of reference choices.

## Reverse map and inverse identities

Given S in Z_2^loc, choose local witnesses b_v. For any edge uv, put w(uv)=b_u(t)+b_v(t) for any incident t. Across a face containing uv both local potential values change by S(f); edge-star connectivity gives choice independence. A triangle lies in one tetrahedron, so its w sum vanishes by pairwise cancellation.

If b'_v is another witness, b_v(t)+b'_v(t) is constant across vertex-star face adjacencies; vertex-star connectivity implies it is a constant A(v) on that star. Therefore changing witnesses changes w by delta A. If S is changed by dB, choose witnesses b_v+B restricted to stars; their edge differences do not change. Consequently the reverse map is well-defined on the quotient and is linear by choosing summed witnesses.

Starting with w, choose the canonical forward witnesses b_v^w. Their differences on uv equal w(uv) by the triangle identity, so reverse-after-forward is the identity in H^1. Starting with S and witnesses b_v, choose B(t)=b_{r(t)}(t). The derived w satisfies w(v,r(t))=b_v(t)+B(t). Thus S_w(f)=S(f)+B(t)+B(t'), so forward-after-reverse is the identity in Z_2^loc/B_2.

These identities prove the claimed isomorphism and yield an explicit obstruction witness in either direction. In particular if H^1=0 then all locally solvable cycles are tetrahedron boundaries. No rank comparison, Euler identity, barycentric fan disk construction, or global dual graph connectivity is required. When local H1 vanishes, each S has local witnesses by restricting its coefficients to the vertex link as in G2_local_potential_gluing.md. The result then applies to every face cycle.

## Formal boundary and tests

G2LocalPotentialGluingCandidate.lean implements the implication from local potentials plus primal cocycle exactness to a global boundary in an abstract incidence interface. It imports only Mathlib and contains four #print axioms queries. No Lean compiler is installed in this session; NOT_RUN, not a verified artifact. It does not yet formalize the inverse map, the link-to-star incidence transport, or the geometric cocycle exactness lemma. The previous missing Mac dependency has not been repaired or retried. The abstract theorem is conditional and not a replacement for those obligations.

Run python3 verify_g2_obstruction_isomorphism.py alongside verify_g2_local_potential_gluing.py. Tests use exact F2 bit arithmetic, compute actual quotient ranks, verify the forward map on cocycle bases and zero, and test both inverse identities modulo boundaries. Reverse samples are exhaustive on three stellar S3 fixtures; only zero and basis on S2 x S1 and suspension torus. The singular suspension has H^1=0, H_2 dimension 2, and locally solvable quotient dimension 0, demonstrating why local H1 cannot be omitted. Finite tests do not establish a general theorem or topology recognition. No repository writes, Codex or Claude. GLOBAL_POINCARE := OPEN.
