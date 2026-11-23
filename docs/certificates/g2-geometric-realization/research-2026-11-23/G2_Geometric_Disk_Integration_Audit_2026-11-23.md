# G2 geometric disk: subdivided cone and integration audit

**Date:** 2026-11-23  
**STATUS:** `PROVED` for the abstract tagged-intersection lemma and the classical PL gluing implication; `SOURCE_AUDITED` for cited repository declarations; `CONDITIONAL` for the application of those declarations; `NOT_RUN` for new Lean code.  
**No repository modification or Git operation.**

## 1. Exact source and execution boundary

Source audited: `inaciovasquez2020/poincare-new-derivation`, published branch `work/first-nonzero-reentry-20261027`:

- `lean/Poincare/PR199G2VerifiedConeComplex.lean`, Git blob `ef91ca5df95415f4d617bd64a7aa31afed626aad` (1,203 lines).
- `docs/certificates/g2-geometric-realization/G2WitnessFreeAffineVerified.lean`, Git blob `b198a04ea9b11733064e82ef16fcb9861f99a8ff` (3,950 lines).
- Archived receipt on the same branch: source-specific Lean 4.30.0-rc1 exit 0; admissible axiom audit PASS, at research checkpoint `61544266b52c6de206bac6acfa41d89b90b15c37`. No new compilation was performed.

Local Mac report (not independently accessed): `HEAD 570f125477cbd89e25055cbbd917bed5a2aa9ef1`, branch `proof/tksv-local-descent`, only `.DS_Store` and `artifacts/.DS_Store` untracked, ~17.03 GiB free. The first direct carrier compiler error is `Mathlib/Analysis/Convex/Combination.olean: invalid header`; the file is reported dataless. A historical audit reported ~86,820 dataless Mathlib artifacts. No bulk recovery or new build is justified for this checkpoint.

## 2. Correct abstract complex

Write `V` for the full fan-graph vertex type and `E` for the type of graph edges, each equipped with its two endpoints. Define the incidence set

    I = {(g, σ) : g ∈ E and σ ∈ g}.

The vertices of the subdivided cone are the disjoint union

    {c} ⊔ {t_σ : σ ∈ V} ⊔ {f_g : g ∈ E}.

For every `z=(g,σ)∈I`, include the two-simplex

    Δ_z = {c, t_σ, f_g}.

The original `fanConeTriangle` has one simplex `{c,t_σ,t_ρ}` per edge `{σ,ρ}`. It is not the same triangulation: it has |E| triangles rather than 2|E|. Its edge subdivision gives exactly the incidence complex above.

**Proposition A (abstract intersection, proved):** For all `z=(g,σ), w=(h,τ)∈I`,

    Δ_z ∩ Δ_w
      = {c}
        ∪ (if σ=τ then {t_σ} else ∅)
        ∪ (if g=h then {f_g} else ∅).

Proof: the three vertex kinds are disjoint by construction. A tetrahedron-tagged vertex lies in `Δ_z` iff its index is `σ`; a face-tagged vertex lies in `Δ_z` iff its index is `g`. The central vertex belongs to every simplex. This handles all four equality patterns with no hypothesis about fan degree.

**Proposition B (abstract disk, proved):** If the original fan graph is a simple cycle with n≥3 vertices and n edges, the incidence graph is the cycle C_(2n). Its cone is therefore a PL closed disk. The boundary is precisely the union of incidence edges `{t_σ,f_g}`, with every such edge contained in one triangle and every radial edge in two. The elementary PL homeomorphism is supplied by mapping incidence vertices to successive points of a convex regular 2n-gon, `c` to the polygon center, and extending affinely on each triangle.

## 3. Actual geometric realization

Let `K` satisfy `ClosedTriangulationCore K`, fix `v,x`, and let `F : AmbientEdgeCyclicFan K v x`. The archived source defines an equivalence

    E : BarycentricDualFlag K {v,x} ≃ I
      := barycentricFlagGraphEndpointEquiv hcore F.

For `z=(g,σ)` write `A_z = E.symm z` and `e={v,x}`. Define

    Φ(c)   = finiteBarycenter e
    Φ(t_σ) = finiteBarycenter (F.tetAt σ).verts.toFinset
    Φ(f_g) = finiteBarycenter (face corresponding to g).

Extend affine-linearly to every triangle `Δ_z`. The source `barycentricEdgeDualCell_eq_graphIndexedUnion` identifies the union of the geometric triangles with the barycentric dual cell.

**Two critical compatibility lemmas for Lean:**

    (A_z.face = A_w.face) ↔ (z.1 = w.1)

and

    (A_z.tet.verts.toFinset = A_w.tet.verts.toFinset)
        ↔ (z.2.1 = w.2.1).

The first follows from `graphEdgeForFaceEquiv` and uniqueness of the third vertex of a represented face, using the definition of `incidentPairToBarycentricFlag`. The second uses the fact that the endpoint-to-tetrahedron map inside `strictFaceEndpointTetEquiv` is `F.tetAt`, its injectivity, and `hcore.eq_of_mem_of_sameTetVertices` to convert equality of supports into equality of tetrahedra. These implications follow from inspected definitions, but their Lean statements/proofs have **not** been compiled.

**Proposition C (conditional PL embedding):** Assuming the two compatibility lemmas, `closedCore_graphIndexed_completeIntersection` identifies the set-theoretic intersection of each pair of genuine flag triangles with the affine image of `Δ_z∩Δ_w` in Proposition A:

- `z=w`: the whole geometric triangle;
- `g=h`, `σ≠τ`: the center-to-face segment;
- `g≠h`, `σ=τ`: the center-to-tetrahedron segment;
- `g≠h`, `σ≠τ`: the center barycenter only.

The affine map of each simplex is injective: choose coordinates on `e`, `face\e`, and `tet\face`. Their barycenter values yield an upper triangular nonsingular coefficient matrix (diagonal 1/2, 1/3, 1/4). The archived certificate contains `actualFlag_affine_coefficients_unique_no_witnesses` (with its necessary tetrahedron-cardinality premise) and the closed-core flag cardinality theorem.

On shared simplex faces, vertex prescriptions agree, so the affine pieces paste to a continuous map from the finite PL realization. Injectivity follows because equality of images forces both preimages into a common simplex face by the exact intersection formula, where their barycentric coordinates agree. The image is exactly the dual cell. A continuous bijection from compact to Hausdorff is a homeomorphism. Compose with Proposition B to obtain the desired disk homeomorphism.

**Important:** `ContractibleSpace` from `barycentricEdgeDualCell_star_segment` is a genuine weaker consequence, not a replacement for the disk assertion or its embedded boundary polygon.

## 4. New chain-level corollary (proved, paper)

Let the cyclic tetrahedron indices be `i∈Z/nZ` and let `g_i` be the edge from `i` to `i+1`. Orient the two subdivided cone triangles over each `g_i` as

    [c,t_i,f_i]  and  [c,f_i,t_(i+1)].

In the integral simplicial chain group define

    D := Σ_i ([c,t_i,f_i] + [c,f_i,t_(i+1)]).

By the alternating-boundary formula,

    ∂[c,t_i,f_i]     = [t_i,f_i] - [c,f_i] + [c,t_i],
    ∂[c,f_i,t_(i+1)] = [f_i,t_(i+1)] - [c,t_(i+1)] + [c,f_i].

Summing cancels the opposite `[c,f_i]` contributions within each pair; it also cancels `Σ_i([c,t_i]-[c,t_(i+1)])` by cyclic reindexing. Hence **over the integers**, and therefore mod 2,

    ∂D = Σ_i ([t_i,f_i] + [f_i,t_(i+1)]).

This is precisely the oriented `2n`-edge incidence-subdivision boundary cycle, with each boundary edge occurring once. It proves a chain-level local filling identity independent of the particular geometry, as soon as a cyclic fan exists. The geometric image identifies the chain with the genuine dual-cell disk only **conditional on the PL embedding compatibility lemmas**. This identity does not establish that arbitrary global mod-2 dual-graph cycles are generated by these boundaries; that remains a separate global topological obligation.

## 5. Recommended minimal formalization order

1. Compile the attached candidate `G2SubdividedConeCandidate.lean` in a *compatible* existing Lean environment, or keep it `NOT_RUN` while dependencies remain offloaded. It defines the tagged vertices and proves the card-three and exact intersection lemmas without placeholders. Candidate only; Lean compilation has not happened.
2. Integrate the existing archived certificate as an importable G2 geometry module **only after** dependencies and existing source collisions are checked. Merely importing `PR199G2VerifiedConeComplex` does not expose the archived geometric declarations.
3. Prove the two compatibility lemmas against exact definitions. Stop and repair the first failing lemma before adding the next.
4. Construct the finite triangulation and piecewise-affine map; prove `continuous`, `injective`, `range = barycentricEdgeDualCell`, then the disk-homeomorphism.
5. After compiling against pinned Lean 4.30.0-rc1 and Mathlib `05c4d64...`, run `#print axioms` on every new load-bearing theorem. Allowed: `propext`, `Classical.choice`, `Quot.sound`. No commit, push, merge or deletion without authorization.

## 6. Status

`ABSTRACT_SUBDIVIDED_INTERSECTION := PROVED` (paper); `INCIDENCE_BOUNDARY_CHAIN_IDENTITY := PROVED` (paper); `ABSTRACT_CONE_DISK := PROVED` (paper); `GEOMETRIC_INDEX_COMPATIBILITY := SOURCE_DERIVED, NOT_LEAN_VERIFIED`; `GLOBAL_PL_GLUING := CONDITIONAL`; `G2_DISK_HOMEOMORPHISM := NOT_LEAN_VERIFIED`; `GLOBAL_POINCARE := OPEN`.
