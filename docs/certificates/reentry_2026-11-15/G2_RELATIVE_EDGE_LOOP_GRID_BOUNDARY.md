# Relative boundary proof for primal edge loops via positive-coordinate grids

**Status: CONDITIONAL PAPER DERIVATION; Lean integration NOT_RUN.**
**Goal:** Establish the actual-carrier implication `SimplyConnectedSpace(|K|) → ker δ₁ = im δ₀` using source-visible finite-grid lemmas. This is a theorem about primal edge cocycles, not the unrelated recurrent Move32 loop.

## Existing, inspected sources

- `lean/Poincare/TriangulationTopologicalSimplyConnected.lean` defines genuine `TriangulationRealizationSimplyConnected K := SimplyConnectedSpace (triangulationTopologicalGeometricCarrier K)`.
- `lean/Poincare/GlobalMove32ReentryWholeCarrierLoop.lean` defines `CarrierLoopNullHomotopyData` with boundary equations and `exists_carrierLoopNullHomotopyData` for every carrier loop.
- `lean/Poincare/GlobalMove32ReentryPolygonalLoopNullHomotopy.lean` proves uniform coordinate positivity on sufficiently fine square-grid cells for any such homotopy.
- `lean/Poincare/GlobalMove32ReentryDyadicGridVertices.lean` provides `exists_finite_squareGrid_positiveCoordinate_labelling_probe` and `carrier_two_positive_coordinates_common_tet_probe`.
- At remote PR #200, `carrier_finite_positive_coordinates_common_tet_probe` and `squareGrid_commonPoint_labels_common_tet_probe` have passed dedicated CI, giving **one** tetrahedron containing *all* labels at a common grid point, stronger than pairwise compatibility.

## Relative finite-grid lemma (proof target)

Let `K` be a finite represented simplicial complex with injective vertex-basis realization and correctly represented faces. Let `γ` be a continuous loop obtained by concatenating straight *primal edge* segments between vertices `v₀,...,v_m=v₀`. Let `H` be a relative null-homotopy of `γ`. Choose a sufficiently fine square grid with:

1. one strictly positive-coordinate label on each **closed** grid cell;
2. all boundary times at which `γ` reaches a primal vertex aligned to grid lines (using an appropriate multiple of `m`; this is **not** automatically the dyadic transition lemma for recurrent Move32 paths);
3. at least two cells in each direction.

Form the *dual cell-center grid*: vertices correspond to squares indexed `(i,j)`, adjacent labels are connected through their common grid-side point. For each internal grid node, four incident square labels are jointly contained in a represented tetrahedron by `squareGrid_commonPoint_labels_common_tet_probe`. Triangulate that dual quadrilateral along a fixed diagonal. Each triangle's three labels lie in the tetrahedron and thus form an allowed 2-simplex, or its normalized chain is zero if labels repeat.

Sum all these triangles modulo two. Internal dual-grid edges occur twice and cancel. The resulting boundary 1-chain is the sum of perimeter dual-grid edges, with a concrete cyclic order. This cancellation can be verified purely by a finite incidence calculation, independent of geometry.

At the three constant sides of `H`, every boundary cell's label equals the unique original vertex `v₀`, because its coordinate is the only positive coordinate at the constant carrier point. Thus those boundary edges vanish as normalized simplicial chains.

On the remaining boundary side, each closed boundary cell interval lies in a single primal segment `[v_k,v_{k+1}]`. Strict positive-coordinate membership forces its label to be one of `v_k,v_{k+1}`, by the basis-coordinate form of the straight segment. At the grid line joining successive primal segments, the label of each touching cell must equal `v_k` (uniqueness of positive coordinate at that carrier vertex), so the boundary-cell word within each original edge segment starts at `v_k` and ends at `v_{k+1}`. Its mod-two edge chain therefore equals that original primal edge, since transitions `u→v` occur with odd parity exactly when endpoints differ, while repeated vertices contribute zero. Summing segment by segment, the perimeter 1-chain equals the original edge loop's mod-two chain.

**Careful endpoint issue:** The dual-grid perimeter runs through *cell centers*, not the original boundary parameter nodes. One must check the first and last boundary cell on every segment touch the breakpoint vertex, and that the dual-grid corners at the ends of the active side are on constant sides. Without those incidence and endpoint statements, exact boundary identification is still **OPEN in Lean**. For arbitrary edge-loop parameterizations, the grid scale must be refined to align every segment boundary (an integer multiple of the number of segments suffices for equal-duration edge traversal).

Hence the loop 1-chain bounds an explicit `F₂` 2-chain of primal triangles, provided these endpoints and triangulation coefficients are discharged.

## Cocycle exactness derivation

Let `w : Edge K → F₂` satisfy `δ₁ w=0`, i.e. the sum of its three edge coefficients vanishes on each primal triangular face. Pair it with the preceding finite filling of any closed primal edge walk `γ`. Each triangle contributes zero, so `⟨w,[γ]⟩=0`.

If the primal 1-skeleton is connected, choose root `v₀`. Define `a(v)` as the `w`-sum along any edge path from `v₀` to `v`; the closed-walk result establishes path independence. For each oriented/unoriented primal edge `uv`, `a(u)+a(v)=w(uv)` in `F₂`. Thus `w=δ₀ a`. The converse `δ₁ δ₀=0` is combinatorial. Therefore `ker δ₁=im δ₀`.

## Exact remaining Lean obligations (not mere declarations)

1. Construct the **actual** carrier edge path for arbitrary finite primal edge walks, and prove it has the prescribed vertex-based boundary trace.
2. Prove grid subdivision can simultaneously satisfy strict positive-coordinate closed-cell control, `D≥2`, and alignment of **all** edge-loop breakpoints.
3. Prove the triangle-chain incidence cancellation for the dual cell-center grid, including degenerate repeated labels.
4. Prove the three constant sides' boundary chains vanish and the active side matches the *original primal edge-chain*, with the endpoint/corner indices checked.
5. Establish the potential `a` and transport the theorem to the actual finite `δ₀,δ₁` rank types, audit axioms and check nonvacuity.

No dependency on geometric embedded G2 disks or a separate `H₁(D)` theorem is necessary for this route. The proof remains **paper only** until obligations 1–5 are compiled in the actual repository.

**Checkpoint:** No Mac repository edits, no merge, no claims of Lean proof for the carrier-to-edge-path bridge. **GLOBAL_POINCARE := OPEN**.
