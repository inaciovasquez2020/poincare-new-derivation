# G2 unified simplicial cocycle cancellation

Status: PROVED_ON_PAPER (standard finite simplicial topology and linear algebra); finite algebraic regression COMPUTATION_PASS; Lean NOT_RUN. No global Poincaré claim. Source audit reference: poincare-new-derivation commit ffbd449d21530c1bef49c7b8cfac1cd89b3a2bd5 (last reported Mac HEAD); PR #200 head 36df38d563014164bf288d17448255de4817abb8. No repository modifications or external delegation.

## 1. General theorem

Let L be a nonempty finite abstract simplicial complex with vertices V and standard realization X inside R^V (unit coordinate vectors e_v). A point has nonnegative coordinates summing to one and its positive-coordinate support is a simplex. Let X be simply connected. Let w be an F2 edge cochain, extended symmetrically and by zero on the diagonal (arbitrary values on nonedges do not matter). Suppose w(a,b)+w(b,c)+w(c,a)=0 whenever {a,b,c} is a simplex, including repeats. Then w is a vertex coboundary. In particular every closed edge walk has zero pairing and H_1(L;F2)=0.

### Exact loop construction

For a closed edge walk v_0,...,v_m=v_0 with m>0, define gamma(t) for k/m <= t <= (k+1)/m by

  gamma(t) = (1-(mt-k)) e_{v_k} + (mt-k)e_{v_{k+1}}.

Each restriction lands in the represented edge (or a single vertex for a repeat). The restrictions agree at all common endpoints. The finite closed-cover pasting lemma gives continuity into X. Hence gamma is a based loop. The empty walk has pairing zero directly. This construction requires no recursive dyadic concatenation theorem. Simple connectivity yields a continuous relative null homotopy H: [0,1]^2 -> X with H(0,t)=gamma(t), H(1,t)=e_{v_0}, H(s,0)=H(s,1)=e_{v_0}.

### Grid node labels

Set d=|V| >= 1. Every point in X has at least one coordinate >=1/d. By uniform continuity of the finitely many coordinate functions of H on the compact square, there is delta>0 such that points at sup distance <delta have coordinate differences <1/(2d), simultaneously for every coordinate. Choose positive N divisible by m, with 1/N<delta. At node (i/N,j/N), choose a label l(i,j) with coordinate >=1/d at its image. That coordinate is positive at the image of every point in every closed cell incident to that node. In particular all four corner labels of a cell are positive at the image of its southwest corner. Thus their set is contained in a SINGLE simplex of L. Mere pairwise edge compatibility is insufficient; this stronger assertion follows from support. All grid-neighbor edges and the chosen cell diagonals are represented or degenerate.

### Cell and boundary cancellation

A cell with consecutive corner labels a,b,c,d' has perimeter weight zero: add the triangle identities for (a,b,c) and (a,c,d'); the diagonal term appears twice. Sum over all N^2 cells. Every interior grid edge appears twice, leaving precisely the outer perimeter, of weight zero. On the three constant sides, positivity forces every node label to be v_0. Consequently the sum on the loop side is zero.

The node j=kN/m on the loop side has image e_{v_k}, so its label is v_k. Between this anchor and the next, every label lies in {v_k,v_{k+1}}, by support of the affine edge segment. If these endpoints coincide, every summand is zero. Otherwise each local word toggles between the two labels an odd number of times, since it starts at the first and ends at the second. Equivalently, the binary indicator of the second label telescopes over F2. The block sum equals w(v_k,v_{k+1}). Summing all blocks proves the closed-walk pairing is zero. No strict distinctness assumption is needed; repeated vertices are permitted.

### Vertex potential and H_1

The 1-skeleton is connected: if its vertices have more than one graph component, the union of simplices of one component and the union of all remaining simplices are disjoint nonempty closed sets partitioning X (simplices are finite and each simplex has all its vertex pairs joined). This contradicts connectedness. Pick a base vertex and define A(v) as the w-sum on any edge path from the base to v. Reversing and concatenating two such paths gives a closed walk, whose pairing vanishes. Thus A is independent of choices and A(u)+A(v)=w(u,v) on represented edges.

Let C_i denote finite F2 chain spaces and partial_i the ordinary simplicial boundaries. For any z in ker partial_1, assume z not in im partial_2. Finite linear algebra supplies a linear functional lambda on C_1 annihilating im partial_2 with lambda(z)=1 (extend a basis of im partial_2 by z and then to a basis of C_1). Its edge values give exactly a symmetric triangle-cocycle w. The result above yields w=delta A. Then lambda(z)=<A,partial_1 z>=0, contradiction. Since partial_1 partial_2=0, ker partial_1=im partial_2. This is an elementary dual-annihilator argument, not an invocation of homology comparison or Poincaré duality.

## 2. Repository instantiations

- Whole carrier: `triangulationTopologicalGeometricCarrier K`; actual `TriangulationRealizationSimplyConnected K`; `carrier_exists_finite_barycentric_support`, `convexHull_geometricVertex_image_exists_weights`, `geometricVertex_weighted_sum_coordinate` in CarrierPositiveCoordinateCover.lean establish the geometric coordinate mechanism.
- Vertex link: `triangulationTopologicalVertexLink K v`; `mem_triangulationTopologicalVertexLink_iff` realizes it as the union of convex hulls of represented link triangles. The same convex-hull weight/coordinate theorems apply to triangle vertex finsets. Use `triangulationTopologicalVertexLink_simplyConnected_of_topologicalThreeManifold` to provide simple connectivity for supported v. Use actual canonical `VertexLinkMod2Edge`, `VertexLinkMod2Vertex`, `VertexLinkMod2Triangle` and their matrix incidence definitions in VertexLinkMod2Chain.lean. The local H1 conclusion must be transported to these exact types, checking no repeated or missing edges/triangles.
- Local potential gluing: prior proof G2_local_potential_gluing.md supplies H2 exactness once the local H1 and global cocycle exactness are available. Edge-star connectedness is available as `vertexLinkStarConnected_of_topologicalThreeManifold`; actual local potential incidence and global gluing in Lean remain open.

## 3. Minimal Lean architecture (not implemented or verified here)

Generic finite simplex-family realization, with the support of each point contained in a represented simplex and all coordinates nonnegative summing to one. Construct equal-time affine path by finite closed-set pasting. Prove generic node labels from compact uniform continuity, then rectangular grid perimeter cancellation (one-cell two-triangle identity plus finite sum). Force exact anchors on a multiple-of-m grid; prove two-label block cancellation including coincident endpoints. Prove potential independence via closed walk; finite dual-annihilator exactness. Instantiate twice against actual geometric types. The separate bridge from standard simplex family to repository incidence is not assumed solved.

## 4. Verification boundary

The companion Python script exhaustively checks finite grid-label cancellation on two specified small complexes, including nonexact cocycles on an annulus, and two-label words through 12 transitions. Its negative control demonstrates pairwise-only compatibility does not imply triangle filling. These are algebraic regression checks, not a verification of continuous homotopy existence, compactness, or Lean. The previous Mac compilation route remains BLOCKED by a genuinely missing `.olean` and was not retried. This new architecture replaces the prior thirteen-module G2 route at the paper level only. It is standard mathematics; no independent novelty review was done. GLOBAL_POINCARE := OPEN.
