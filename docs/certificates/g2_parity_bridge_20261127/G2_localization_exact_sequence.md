# G2 localization exact sequence and independent rank audit

2026-11-27. PROVED_ON_PAPER under explicit incidence and connectivity hypotheses; COMPUTATION_PASS for eight finite fixtures; Lean NOT_RUN. No novelty claim or global Poincare claim.

## Theorem

Let K be a finite pure simplicial 3-complex, with two distinct tetrahedra incident to every represented triangular face. Assume that for each represented vertex and each represented edge, its incident tetrahedra form a connected graph under adjacency across triangular faces containing that vertex or edge, respectively. All coefficients are F2.

For a 2-chain S define r_v(S) on the link of v by assigning to each link edge e the coefficient S({v} union e). Define r_v on a 3-chain B by assigning to each link triangle sigma the coefficient B({v} union sigma). Then

* If S is a 2-cycle, r_v(S) is a link 1-cycle: at a link vertex u, the boundary coefficient is the coefficient of the primal boundary of S at the edge {v,u}.
* r_v(partial_3 B) = partial_2 r_v(B), by the bijection between tetrahedra containing a face containing v and link triangles containing the corresponding link edge.

Thus R([S]) = ([r_v(S)])_v defines a linear map from H_2(K;F2) into the direct sum of link H_1 spaces.

Its kernel is exactly Z_2^loc/B_2. Indeed R([S])=0 iff each r_v(S) is the boundary of a link 2-chain. By the tetrahedron/link-triangle bijection these are precisely the local star potentials with coface sum S(f) for each face containing v. This equivalence involves actual boundary maps, not merely dimension equality.

The explicit forward and reverse maps proved in G2_obstruction_isomorphism.md identify this kernel with H^1(K;F2). Consequently the following sequence is exact (no surjectivity assertion at the final space):

    0 -> H^1(K;F2) -> H_2(K;F2) --R--> direct_sum_v H_1(lk_K(v);F2).

In particular there is a short exact sequence with final space im R and a terminal zero. Therefore

    b_2(K) = b_1(K) + rank R.

Here b_1 is also dim H^1 by finite-dimensional duality over F2. In the closed 3-manifold case the link H_1 spaces vanish and R is zero. In the simply connected case b_1=0, so R is injective. Both hypotheses together give H_2=0. This is a standard-type local-to-global homological argument; no claim of novelty or an independent proof of the Poincare conjecture.

## Sharp negative control: suspensions

Let L be a connected closed triangulated surface and K its simplicial suspension, with apices p,q. Use the natural identifications lk(p)=lk(q)=L. A 2-chain decomposes uniquely as S=p*a+q*b+c, with a,b 1-chains and c a 2-chain of L. If S is a cycle, the cone boundary formula gives partial a=partial b=0 and a+b=partial c. Hence R at the apices is ([a],[a]); all non-apex vertex links are suspensions of vertex-link circles, hence 2-spheres and have zero H_1. Conversely each link cycle a gives the global cycle p*a+q*a. Thus im R is exactly the diagonal of H_1(L) direct_sum H_1(L), not the whole direct sum unless H_1(L)=0.

The suspension is simply connected (cover by two contractible open neighborhoods of the cones with path-connected intersection). Therefore the localization map is injective and b_2(K)=dim H_1(L). For an orientable genus-g surface the localization rank is 2g, the target dimension 4g. This proves that the residual local obstruction can be arbitrarily large despite simple connectivity; and that R need not be surjective. It does not contradict the manifold case: the apex links are not spheres for g>0.

## Independent computation

Run `python3 verify_g2_localization_rank.py` with `verify_g2_local_potential_gluing.py` in the same directory. The new verifier uses the earlier fixture geometry but an independent GF(2) row-reduced echelon implementation, explicitly constructs every local incidence matrix and reduces restrictions modulo local boundaries. It checks each global cycle-basis vector, every global tetrahedron boundary generator, and every basis vector of the calculated kernel. It computes rank R directly, NOT as b2-b1. All eight fixture results are recorded in g2_localization_rank_receipt.json. Finite checks are exhaustive on the indicated generating sets and do not constitute unrestricted formal proof. Three torus subdivisions and a genus-two suspension test the sharp negative control. Fixture geometry identification is classical and not Lean-verified. Fixed finite fixture sizes are guarded.

## Reporting correction and open boundary

The earlier `local_obstruction_quotient_dimension` field is dim H_2 minus dim(Z_2^loc/B_2), i.e. rank R. It is not dim(Z_2^loc/B_2). This receipt reports `localization_rank` and `locally_solvable_quotient_dimension` separately and calculates both directly.

The abstract Lean forward-gluing candidate remains unchanged and uncompiled. No Lean binary is present in this session, and the Mac dependency failure has not been retried. Formalizing actual link incidence transport, geometric cocycle exactness and the localization maps remains OPEN. No repository writes, Codex, or Claude. GLOBAL_POINCARE := OPEN.
