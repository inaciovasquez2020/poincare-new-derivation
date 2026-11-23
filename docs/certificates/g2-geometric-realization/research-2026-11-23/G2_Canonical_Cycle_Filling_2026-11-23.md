# G2 cyclic cone — exact integral cycle-filling theorem

**Date:** 2026-11-23. **Status:** `PROVED` (mathematics, over `ℤ` and any commutative coefficient ring); `LEAN_VERIFIED := NO` for this new theorem; no Mac / Git actions.

## Assumptions and indexing

Let `n≥3` and let the ambient cyclic-fan graph be a single simple cycle with `n` tetrahedral vertices and `n` face-index edges. Let `m=2n`. The abstract edge-subdivided polygon has distinct vertices `u_0,…,u_(m−1)` cyclically ordered; the subdivided cone has an additional vertex `c`. Orient the boundary edges `b_i=[u_i,u_(i+1)]`, the radial edges `r_i=[c,u_i]`, and the triangular faces `s_i=[c,u_i,u_(i+1)]`, with all subscripts modulo `m`.

The simplicial boundary formula holds integrally:

`∂s_i = b_i − r_(i+1) + r_i`.

There are exactly `m` triangles, `m` boundary edges, and `m` radial edges. All triangles meet at `c`, and each boundary edge belongs to exactly one triangle.

## Theorem: canonical and unique filling of EVERY local 1-cycle

For **every** integral simplicial 1-cycle `z` of this cone, there exists a **unique** integral 2-chain `Q` with `∂Q=z`. Moreover, the inverse of the boundary map is explicit and linear.

Write the unique edge expansion of any 1-chain as

`z = Σ_i (a_i b_i + q_i r_i)`, with `a_i,q_i∈ℤ`.

Because `∂b_i=u_(i+1)-u_i` and `∂r_i=u_i-c`, the coefficient of `u_i` in `∂z` is `a_(i−1) − a_i + q_i`. If `∂z=0`, then necessarily

`q_i=a_i−a_(i−1)` for each `i`.

Define the 2-chain `Q=Σ_i a_i s_i`. Its boundary satisfies

`∂Q=Σ_i a_i b_i+Σ_i(a_i−a_(i−1))r_i=z`.

This proves **existence** with no division or homological abstract machinery.

For **uniqueness**, suppose `Q'=Σ_i d_i s_i` has `∂Q'=0`. The boundary-edge coefficient of `b_i` in `∂Q'` is exactly `d_i`, since no other triangle contains `b_i`; hence every `d_i=0`, so `Q'=0`.

Therefore

`∂₂ : C₂(cone(C_m);ℤ) ≃ₐ Z₁(cone(C_m);ℤ)`

is an isomorphism of abelian groups (indeed of free `ℤ`-modules), with inverse `z↦Σ_i coeff_(b_i)(z)·s_i`.

The argument uses only coefficients `0,±1` and never division, so it holds over any commutative ring `R`, including `𝔽₂`. In particular, `H₁(cone(C_m);R)=0` and `H₂(cone(C_m);R)=0`.

## Explicit boundary-cycle certificate

Taking all `a_i=1` gives `q_i=0` and the unique filled boundary polygon:

`∂(Σ_i s_i)=Σ_i b_i`.

Translating to the original fan indexing: `u_(2i)=t_i`, `u_(2i+1)=f_i`, and

`Σ_i s_i = Σ_i ([c,t_i,f_i]+[c,f_i,t_(i+1)])`,

whose boundary is `Σ_i ([t_i,f_i]+[f_i,t_(i+1)])`.

## Scope boundary

This is a fully unconditional theorem about an **abstract cone of a single finite cycle**. Identifying this cone with the *actual geometric dual cell in the carrier* still requires the geometric index-compatibility lemmas, the affine simplex embeddings, and the continuous injective gluing map; those remain `NOT_LEAN_VERIFIED`. It does not imply arbitrary global dual-graph cycles lie in the span of local G2 disk boundaries and does not prove universal descent or Poincaré.

## Lean integration status and candidate

The archived repository certificate defines `barycentricFlagGraphEndpointEquiv`, `graphEdgeForFaceEquiv`, `incidentPairToBarycentricFlag`, and the relevant face/tetrahedron incidence equivalences. Its archived receipt reports Lean 4.30.0-rc1 compilation and axiom audit PASS at a prior research checkpoint. The attached **single-lemma** proof candidate `G2_FlagFaceProjection_Candidate_2026-11-23.lean` isolates the face-projection part of the missing index compatibility. It requires concatenation with the standalone archived certificate and is `NOT_RUN`; `rfl` is a proposed proof and **not** a verified compiler result.

The Mac checkout last reported `570f125477cbd89e25055cbbd917bed5a2aa9ef1`, branch `proof/tksv-local-descent`, with two untracked `.DS_Store` files. The first carrier build error remained an offloaded `Mathlib/Analysis/Convex/Combination.olean`. No repository changes, merges, pushes, or dependency recovery attempted here.

## Reproducible exact-arithmetic check (secondary evidence)

`g2_canonical_filling_verify.py` exhaustively tested all `3^6=729` and `3^8=6561` possible triangular coefficients in `{-1,0,1}` and each standard basis triangle for `m=6,8`. The test computes the simplicial boundary maps independently in integer coordinates, checks `∂₁∘∂₂=0`, and verifies the coefficient formula for the unique filler.

`EXACT_INTEGER_CHECKS := 7304`; `RESULT := COMPUTATION_PASS`; `LEAN := NOT_RUN`. This finite check is secondary to the unrestricted algebraic proof; it is not a formal certificate.

## Geometric correspondence — direct repository-derived reduction

The published source `G2WitnessFreeAffineVerified.lean` defines a composite equivalence:

`barycentricFlagGraphEndpointEquiv = barycentricFlagIncidentEquiv.trans globalTetGraphEndpointEquiv`,

where `globalTetGraphEndpointEquiv = globalFaceIndexedFlagEquiv.trans faceEndpointGraphEndpointEquiv`. The inverse of `faceEndpointGraphEndpointEquiv` replaces a graph edge `g` by `f=(graphEdgeForFaceEquiv hcore F).symm g` and leaves the underlying endpoint `σ` unchanged. The inverse of `globalFaceIndexedFlagEquiv` maps this endpoint to `F.tetAt σ` using `strictFaceEndpointTetEquiv.toFun`. Finally the inverse of `barycentricFlagIncidentEquiv` applies `incidentPairToBarycentricFlag` with `face=insert f.1 {v,x}` and `tet=F.tetAt σ`. These are source-level definitions; no new Lean elaboration was performed.

Thus for `z=(g,σ)` and `A_z=(barycentricFlagGraphEndpointEquiv hcore F).symm z`, the intended definitional projection equalities are:

`A_z.face = insert ((graphEdgeForFaceEquiv hcore F).symm g).1 {v,x}`

`A_z.tet = F.tetAt σ`.

The first is the exact target of the attached single-lemma candidate. Once both projections compile, the support-index equivalences follow from the injectivity of `graphEdgeForFaceEquiv`, the distinct-third-vertex property of `RepresentedEdgeFace`, and `F.tetAt_injective` together with `hcore.eq_of_mem_of_sameTetVertices`.

**Remaining obstruction:** This source-level computation has not been kernel-checked in the current checkout; the candidate's final `rfl` may encounter non-definitional transports and needs actual elaboration. The archived certificate must be tested without simultaneously importing the overlapping 1,203-line cone module, since both define names in `Poincare.PR199G2`.
