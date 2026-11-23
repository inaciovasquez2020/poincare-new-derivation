# Canonical filling for the cone on any finite simple graph

**Research status:** `PROVED` (mathematical algebraic proof); `COMPUTATION_PASS` (bounded checks); `LEAN_VERIFIED := NO`; `GEOMETRIC_G2_HOMEOMORPHISM := OPEN`; `GLOBAL_POINCARE := OPEN`.

**Date:** 2026-11-23. This theorem extends the earlier cyclic-fan cone filling argument, but does **not** establish that the cone of an arbitrary graph is a disk.

## Statement

Let `G=(V,E)` be any finite simple graph; disconnected graphs, isolated vertices, and the empty graph are permitted. Give each edge `e=(u,v)` an arbitrary fixed orientation. Adjoin a new center `c`, all radial edges `[c,v]`, and, for each graph edge `(u,v)`, the triangle `[c,u,v]`. Write `X = Cone(G)` for the resulting abstract simplicial complex. Let `A` be **any abelian group** of coefficients; no division or choice of a field is needed.

Then the simplicial boundary map induces an isomorphism of abelian groups

`∂₂ : C₂(X;A) → Z₁(X;A) := ker(∂₁)`.

The inverse is **canonical relative to the chosen edge orientation**: for a 1-cycle, extract its coefficients on the original graph edges and use those coefficients on the corresponding cone triangles.

## Proof with explicit matrices

Let `d_G:A^E→A^V` be the ordinary oriented incidence boundary of the base graph. In particular, for an edge oriented `u→v`, its column is `−[u]+[v]`. Then `sum_v(d_G a)_v=0` for every `a∈A^E`.

With bases ordered as **outer graph edges** followed by **radial edges**, there are canonical identifications

`C₂(X;A)=A^E`, `C₁(X;A)=A^E⊕A^V`, `C₀(X;A)=A^V⊕A·[c]`.

The alternating simplicial boundary formula gives

`∂₂(a) = (a, −d_G a)`.

Indeed, for an oriented outer edge `(u,v)`,

`∂[c,u,v]=[u,v] − [c,v] + [c,u]`.

Similarly,

`∂₁(a,q)=(d_G a+q, −Σ_v q_v)`.

If `∂₁(a,q)=0`, its vertex components force `q=−d_G a`. Conversely, for `q=−d_G a`, the vertex components vanish and the center component is `Σ_v(d_G a)_v=0` by cancellation of each oriented edge's two endpoints. Thus

`Z₁(X;A) = {(a,−d_G a):a∈A^E}`.

Consequently `∂₂` is surjective onto `Z₁` and injective because its first coordinate is exactly `a`. The inverse is the projection `Q(a,q)=a`. Both maps are additive, establishing the stated isomorphism. This proof applies to **every** abelian coefficient group and every finite simple graph.

### Corollaries

- `H₁(X;A)=0` and `H₂(X;A)=0` (there are no three-simplices in the cone of a graph).
- If `G=C_m`, the explicit inverse recovers the previous G2 cyclic-cone formula with `m=2n` and its unique integral filling.
- If `G` is not a single cycle, `X` need **not** be a topological or PL disk: for example the cone on a three-spoke star has non-manifold boundary behavior. The chain isomorphism must **not** be used as a disk-homeomorphism theorem.
- This result does not identify the abstract cone with the genuine edge-dual cell in a 3-manifold triangulation. The G2 geometric support-index compatibility, affine gluing, and disk-homeomorphism Lean integration are still open.

## Independent finite verification (executed 2026-11-23)

A dependency-free Python verifier (`g2_general_cone_filling_verify.py`) independently implements the graph incidence boundary and the simplicial `∂₁`, `∂₂` operators. It exhaustively considers **all 76 simple graphs** with `0≤|V|≤4` and **all 11,895 associated F₂-valued 1-chains**. For each graph it also verifies that the number of cycles is precisely `2^|E|`, as the theorem predicts.

Separate reproducibly seeded exact-integer tests cover graph sizes `3,4,5,6,8,12,20`, sparse/disconnected/complete graph patterns, and perturbed noncycles. In all, there are **8,400 integer trial pairs** (`z` and deliberately perturbed noncycle). The code records `28,695` total 1-chain checks, `9,161` successful cycle inversions, and zero failures. Seed `20261123`, wall guard `25` seconds; test elapsed about `0.35` seconds in the inspection environment.

`RESULT := COMPUTATION_PASS` for this finite test suite; the universal theorem is proved by the explicit algebra above, **not** by finite search.

## Source and repository boundary

This proof is independent of the Mac's presently offloaded Mathlib `.olean` objects. The archived `G2WitnessFreeAffineVerified.lean` at branch `work/first-nonzero-reentry-20261027` contains the geometric flag and intersection lemmas, with a historical Lean 4.30.0-rc1 certificate; the G2 disk homeomorphism itself remains **OPEN** in Lean. An uncompiled `G2SubdividedConeCandidate.lean` and a proposed single-lemma `G2_FlagFaceProjection_Candidate_2026-11-23.lean` are included separately as research candidates, **not** as certified source. Do not import them into production or promote their status before compilation and an admissible-axiom audit.

This is a research artifact; it does not change the main theorem, introduce an axiom, or authorize a Git merge.