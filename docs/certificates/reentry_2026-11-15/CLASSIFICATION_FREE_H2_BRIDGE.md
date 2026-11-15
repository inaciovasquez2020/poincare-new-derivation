# Classification-free topology-to-simplicial \(H_2\) bridge

**Mathematical status:** PROVED from standard PL dual-cell facts, without Poincaré classification. **Lean status:** OPEN (geometric-dual-complex bridge unverified). This note records an implementation target, not a kernel certificate.

## Precise target

Let \(K\) be a finite connected simplicial triangulation of a closed PL 3-manifold, and \(X=|K|\). Let \(C_i(K;\mathbb F_2)\) be the finite simplicial chain groups with ordinary mod-two incidence boundary. Then

\[
\pi_1(X)=1 \Longrightarrow
\ker(\partial_2:C_2\to C_1)=\operatorname{im}(\partial_3:C_3\to C_2).
\]

This statement does **not** use Poincaré classification, Perelman, or a sphere-recognition theorem.

## Direct dual-cell proof (avoids Hurewicz and Poincaré duality)

1. Take the barycentric dual CW decomposition \(D\) of the closed PL 3-manifold: dual 0-cells \(t^*\) correspond to primal tetrahedra \(t\), dual 1-cells \(f^*\) to primal triangles \(f\), and dual 2-cells \(e^*\) to primal edges \(e\). The dual 1-cell crosses its primal triangle once. All these dual cells are embedded in the same \(X\). The dual CW complex is homeomorphic to \(X\).
2. For any primal 2-cycle \(S\) define \(\alpha(f^*)=S(f)\in\mathbb F_2\). Around each dual 2-cell \(e^*\), the parity is \(\sum_{f\supset e}S(f)=(\partial_2S)(e)=0\). Thus \(\alpha\) is a cellular 1-cocycle of the dual 2-skeleton.
3. Pick a base dual vertex \(t_0^*\). For any dual edge path \(p\), set \(I_\alpha(p)=\sum_{f^*\in p}\alpha(f^*)\in\mathbb F_2\). Backtracking contributes zero and crossing the attaching boundary of any dual 2-cell contributes zero. The standard CW edge-path presentation therefore makes \(I_\alpha\) constant on endpoint-fixed homotopy classes and gives a homomorphism \(\pi_1(D)\to\mathbb F_2\).
4. Since \(D\cong X\) is simply connected, every closed dual edge walk has \(I_\alpha=0\). By dual 1-skeleton connectivity, define \(B(t)=I_\alpha(p_t)\), for any path from \(t_0^*\) to \(t^*\). It is independent of the path.
5. For each triangle \(f\) with incident tetrahedra \(t,u\), append the dual edge \(f^*\) to a path from \(t_0\) to \(t\). This yields \(B(u)=B(t)+\alpha(f^*)\), hence \((\partial_3B)(f)=B(t)+B(u)=S(f)\).
6. Therefore \(S=\partial_3B\). This proves \(H_2(K;\mathbb F_2)=0\).

The critical PL assumptions are the actual closed *manifold* links and dual cell attaching maps; merely requiring each triangle to have incidence two does not suffice to identify the dual 2-cell relations with the carrier's fundamental group.

## Application to witnessed reentry

An explicitly realized old degree-three site, source-face two-coface condition and nonself complementary edge yield \(S_q=abc+abq+acq+bcq\) with \(\partial_2 S_q=0\). Vertex link connectedness at complementary vertices constructs a path of tetrahedra using faces outside \(S_q\) between the tetrahedra incident to \(abc\). The finite parity lemma forces equality of \(B\)-coefficients along this path if \(\partial_3 B=S_q\), while \(S_q(abc)=1\) forces inequality. This contradicts \(H_2=0\).

## Lean dependency split

- **A: finite parity** `Poincare.DualPathParity.nonboundary_of_avoiding_return`; standalone Lean candidate with dedicated CI audit.
- **B: actual incidence extraction**: instantiate abstract Face/Tet and the two tetrahedra of every represented triangle from `ClosedTriangulationCore`; construct the avoiding path using `VertexLinkConnected.all_of_adjacent_closed` plus `ambientTetOfVertexLinkTriangle`.
- **C: dual CW realization**: construct the barycentric dual 0-,1-,2-cells in `triangulationTopologicalGeometricCarrier K`; prove that the 2-cell boundaries traverse precisely the triangles around each primal edge.
- **D: edge-path homotopy comparison**: show that for a carrier-nullhomotopic dual loop, the crossing parity of any simplicial 2-cycle is zero. Equivalently construct a morphism from the carrier fundamental group to `ZMod 2` whose dual edge values are the cycle's face coefficients.
- **E: use simple connectedness**: apply `SimplyConnectedSpace.paths_homotopic` or triviality of the carrier fundamental group to C/D, construct the tetrahedron potential B, and conclude exactness.

**First load-bearing OPEN formal lemma:** D, with C as its prerequisite. It is NOT a theorem in the current repository and cannot be replaced by an assumed cycle-filling field. Existing Mathlib covering-space and CW definitions do not automatically prove the dual CW comparison.

## Evidence / scope

No new global JIID, Poincaré, or universal witnessed-reentry theorem is claimed. Classical Poincaré classification is not imported. The above is a standard PL-topological proof with a clearly open Lean bridge.
