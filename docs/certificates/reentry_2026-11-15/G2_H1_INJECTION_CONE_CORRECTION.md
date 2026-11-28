# Constructive H₁-injectivity of the barycentric dual subcomplex

**Research status: PROVED on paper (under explicit link-homology hypotheses). Lean: NOT_RUN. Global Poincaré derivation: OPEN.**

## Setup and theorem

Let `K` be a finite simplicial complex, `L=sd K` its barycentric subdivision and `D⊆L` the **full subcomplex on barycentric vertices of primal faces having dimension at least one**. Every simplex of `L` is a chain of strictly nested nonempty faces of `K`, so at most one barycentric vertex in that simplex represents a primal 0-face. For each original vertex `v`, its link `lk_L(v)` is a subcomplex of `D`.

All chains use coefficients `F₂`. Assume for every original vertex `v` that

`H₁(lk_L(v);F₂)=0.`

**Theorem (constructive dual-subcomplex injection).** The inclusion `D ↪ L` induces an injective linear map

`H₁(D;F₂) → H₁(L;F₂).`

Equivalently, every mod-two 1-cycle `z` in `D` satisfying `z=∂c` for some `c∈C₂(L;F₂)` already admits a filling `z=∂c_D'` with `c_D'∈C₂(D;F₂)`.

## Constructive proof

Partition the 2-simplices of `L` into those contained in `D` and those containing precisely one primal 0-face barycenter `v`. Write uniquely

`c = d + Σ_v v * a_v`

where `d∈C₂(D)` and `a_v∈C₁(lk_L(v))`. The cone boundary identity is `∂(v*a_v)=a_v+v*(∂a_v)`.

Since `∂c=z∈C₁(D)`, the coefficient on every edge incident to a primal vertex `v` is zero. Edges incident to distinct primal vertices cannot coincide (a barycentric edge connects strictly nested primal faces), so `∂a_v=0` for each `v`.

By the link-homology hypothesis, choose `b_v∈C₂(lk_L(v))` with `∂b_v=a_v`. Set

`c' := c + Σ_v ∂(v*b_v)`.

Then `∂c'=∂c=z` since `∂²=0`. Moreover

`∂(v*b_v) = b_v + v*(∂b_v) = b_v+v*a_v`,

hence in `F₂` chains

`c' = d+Σ_v b_v ∈ C₂(D)`.

This gives a constructive null-homology filling in `D` and proves the injectivity claim. Nothing requires a geometric deformation retraction or a disk homeomorphism.

## Specialization to the Poincaré setting

For finite closed PL 3-manifold `K`, each original vertex link is PL homeomorphic to `S²`; the link in `L` is its barycentric subdivision, so `H₁(lk_L(v);F₂)=0`. More generally, only these link homology vanishings are necessary for the chain argument.

If additionally `π₁(|K|)=1`, then `H₁(L;F₂)=0` via `|L|≅|K|` and standard simplicial-to-singular homology comparison (or fundamental-group abelianization). Injectivity yields `H₁(D;F₂)=0`.

Combining this with the finite radial-kernel theorem recorded in `G2_RADIAL_CHAIN_DECOMPOSITION.md` shows that any closed subdivided dual-graph walk chain `z` is an `F₂` sum of complete G2 fan boundaries. The explicit dual half-edge cochain pairing then gives zero parity for any primal face 2-cycle, supplying the missing **mathematical** hypothesis of `Poincare.DualPotentialCandidate.potential_of_no_odd_return`. Formal identification of paths, chains, and actual carrier hypotheses is still OPEN.

## Formalization boundary: separate precise components

1. Define `C₁,C₂,C₃` of the actual `sd K` over `ZMod 2` with the ordinary simplicial boundary; verify that `D` is full on positive-dimensional face barycenters.
2. Construct `c=d+Σ_v v*a_v`, the unique decomposition of 2-chain support by the optional original vertex, with finite sums.
3. Prove the cone boundary identity in dimensions 1 and 2, and extract `∂a_v=0` from zero primal-vertex-edge coefficients in `∂c`.
4. Use an **actual** link `H₁=0` theorem to produce `b_v`, carry out the correction `c+Σ_v∂(v*b_v)`, and verify its boundary and support.
5. Separately transport the carrier's simple connectivity to `H₁(L;F₂)=0`, then instantiate the radial-kernel theorem and the dual-walk pairing.

**Do not silently assume** `H₁(lk_L v)=0` from face-incidence-two alone: this requires the relevant local manifold-link hypothesis. Also do not confuse a cycle's `H₁` nullity with an explicit simplicial filling without performing the homology-to-chain step.

No Lean compilation, axiom audit, repo promotion or merge is implied by this paper proof. The local-only source checkpoint `02637eb1…` remains separately preserved on the user's Mac.
