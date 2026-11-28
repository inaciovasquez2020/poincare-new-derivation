# G2 local-potential gluing — 2026-11-27

Status: PROVED_ON_PAPER under stated hypotheses; computation PASS on recorded fixtures; Lean NOT_RUN. Global Poincare OPEN. No novelty claim.

## Theorem
Let K be a finite pure 3-dimensional simplicial complex with exactly two distinct tetrahedra per face. Assume every vertex link has H_1(-; F_2)=0, every represented edge has a connected graph of incident tetrahedra joined along faces containing that edge, and every symmetric F_2-valued primal edge cochain satisfying triangle cancellation has zero pairing with every closed primal edge walk. Then every mod-two face 2-cycle is a tetrahedron 3-boundary. No global Euler counts or dual cycle-space dimension are required.

## Proof
For S in ker boundary_2, put s_v(uw)=S(vuw) in the link of each represented vertex v. Its boundary at u is the sum of S over the faces containing vu, hence zero. Choose a link 2-chain b_v with boundary s_v. Via the bijection between triangles of lk(v) and tetrahedra containing v, write B_v(t)=b_v(t minus v). For every face f containing v with cofaces t,t', the exact two-coface incidence gives B_v(t)+B_v(t')=S(f).

For each represented edge uv choose a containing t and define w(uv)=B_u(t)+B_v(t). On an adjacency across a face containing uv the two summands both change by S(f); the difference is invariant. Edge-star connectivity ensures choice independence. On any represented triangle uvx choose a single incident tetrahedron; the three w values sum to zero by pairwise cancellation. Extend w by zero on nonedges and repeated endpoints if needed by the total Nat-to-Nat cochain interface. Degenerate triangle equations then follow from symmetry and zero diagonal. For each primal graph component choose a basepoint, and define A(v) as the w-sum along a path from the basepoint to v. Closed-walk cancellation and symmetry make it path-independent; w(uv)=A(u)+A(v). Empty and repeated-vertex steps have zero effect.

Define B(t)=B_v(t)+A(v) for any v in t. Independence follows since any two distinct vertices in t form an edge and the sum of the two candidate values is w(uv)+A(u)+A(v)=0. For a shared face f choose a vertex v in f and compute B(t)+B(t')=B_v(t)+B_v(t')=S(f). Thus S=boundary_3 B. Every closed dual walk has zero pairing with S by telescoping. No global dual connectivity is needed.

## Lean frontier
Remote source inspected at ffbd449d21530c1bef49c7b8cfac1cd89b3a2bd5:
- TriangulationTopologicalManifoldVertexLinkSimplyConnectedness.lean: triangulationTopologicalVertexLink_simplyConnected_of_topologicalThreeManifold.
- TriangulationTopologicalManifoldVertexLinkStarConnectedness.lean: vertexLinkStarConnected_of_topologicalThreeManifold; the raw VertexLinkStarConnected path, not its weakened global-link adjacency projection, is needed to preserve the edge.
- VertexLinkMod2Chain.lean: VertexLinkMod2H1Zero is ker boundary_1 = range boundary_2, and vertexLinkMod2_boundary_one_comp_boundary_two exists.

Need actual link incidence transport, link geometric simple connectivity -> link H_1=0, actual closed-primal-walk kernel verification and path integration, then gluing. The link H_1 step can use an appropriately generalized positive-coordinate grid cancellation theorem on the actual triangle carrier plus finite linear duality (ker boundary_1 = range boundary_2 iff every cochain annihilating range boundary_2 annihilates ker boundary_1). A cycle decomposes into closed graph walks. The tetrahedron-specific grid theorem is not directly applicable to a triangle link without adaptation. No assumption of S^3 recognition. Local compile blocked by missing GlobalMove32ReentryPolygonalLoopNullHomotopy.olean; no further rebuild attempted.

## Regression
Run python3 verify_g2_local_potential_gluing.py. Exact integer-bit GF(2) elimination finds a face-cycle basis, then independently compares direct dual graph potentials with local gluing. Three S^3 fixtures: 16+128+1024=1168 cycles exhaustively glued. Product S^2 x S^1: zero and 36 basis vectors, 28 glued, 9 global obstruction. Suspension torus: zero and 37 basis vectors, 27 glued, 11 local obstruction. Basis outcome counts are not independent obstruction dimensions. Topological identifications follow from the explicit constructions, not automated sphere recognition. See JSON receipt. No Codex/Claude; no repo mutation.
