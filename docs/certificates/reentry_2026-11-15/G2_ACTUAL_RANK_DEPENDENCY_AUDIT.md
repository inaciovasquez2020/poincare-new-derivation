# Exact repo declarations for the remaining rank bridge (2026-11-17)

**Status: SOURCE AUDIT / OPEN mathematical integration. No new Lean theorem or axiom verification claimed.**

## Exact verified-source landmarks

At PR #200's research branch, the existing repository contains:

- `lean/Poincare/VertexLinkMod2Chain.lean`: `VertexLinkMod2Vertex`, `VertexLinkMod2Edge`, `VertexLinkMod2Triangle`, `vertexLinkMod2BoundaryOne`, `vertexLinkMod2BoundaryTwo`, `VertexLinkMod2H1Zero` and `vertexLinkMod2H1Zero_iff`.
- `lean/Poincare/VertexLinkMod2BoundaryOneRank.lean`: `vertexLinkMod2BoundaryOne_range_finrank_eq_card_sub_one`, under a connected closed-surface certificate.
- `lean/Poincare/VertexLinkMod2BoundaryTwoRank.lean`: `vertexLinkMod2BoundaryTwo_range_finrank_eq_card_sub_one`, under the corresponding link hypotheses.
- `lean/Poincare/VertexLinkMod2Euler.lean`: **conditional** `vertexLinkEulerCharacteristic_eq_two_of_connectedClosedSurface_and_mod2H1Zero`, requiring `ClosedTriangulationCore K`, `VertexLinkConnectedClosedSurfaceCertificate K v`, a nonempty link triangle type, and `VertexLinkMod2H1Zero K hcore v`.
- `lean/Poincare/PhiSupportEulerCount.lean`: `ClosedTriangulationCore.PhiSupport_add_four_mul_vertices_eq_four_mul_tets`. This is a **vertex-tetrahedron degree-count identity**, not the primal Euler identity `V-E+F-T=0`.

## Consequence for the direct rank proof

The archived paper argument uses `F=2T`, `E=V+T`, rank `δ₁=E-V+1`, and dual cycle rank `F-T+1`. The new Lean rank assembly has correctly compiled in the targeted audit **provided** these input ranks/counts are given. It does not derive them from `ClosedTriangulationCore` or simple connectivity.

**Critical nonvacuity guard:** The existing Euler theorem is conditional on `VertexLinkMod2H1Zero`. Do not silently obtain that hypothesis merely from a `ClosedTriangulationCore` or a `VertexLinkConnectedClosedSurfaceCertificate`; a connected closed surface can have nonzero mod-two `H₁`. Verify that the actual topological manifold certification identifies the vertex links with `S²`, or separately supply a proof of link mod-two `H₁=0`.

There are **two** independent remaining gaps:
1. Actual primal `H¹(K;F₂)=0` from the carrier's simply-connectedness, with a checked simplicial/singular or edge-path comparison.
2. Exact cardinality and rank transport from the existing finite data encodings to primal `V,E,F,T` and the two incidence matrices. The vertex-link Euler formula is a plausible library dependency, but its antecedent must be discharged honestly.

## Latest exact-head CI receipt

At commit `9de259701f99615dddd3b95987821a9d1ac85d00`:
- Targeted `Dual-cell parity relations isolated audit`: **SUCCESS**, both new rank-count assembly declarations reported allowed axioms only.
- `Lean Action CI`: **INCOMPLETE**, dependency retrieval terminated with repeated `SSL_ERROR_SYSCALL` while downloading Mathlib cache artifacts; its Lean build was skipped.
- `Dual-path parity kernel audit`: **INCOMPLETE**, same cache download failure.
- Other specialized workflows completed successfully.

**Do not interpret dependency-download errors as source compile failures, or treat a successful isolated audit as a completed general repository build.**

## Next formalization decision

Prefer one genuine instance of the actual incidence-map rank equation over further generic algebraic lemmas:

`ClosedTriangulationCore K + actual PL local links + SimplyConnectedSpace (carrier K)`
` ⟹ rank(primal δ₁) + V = E + 1`.

The weakest prerequisite is constructing `ker(primal δ₁)=range(primal δ₀)` for the actual carrier. Attempt that before pursuing additional conditional repackagings of the same rank equality.

**LOCAL MAC STATE:** Not inspected. **NO-MERGE**. **GLOBAL_POINCARE := OPEN**.
