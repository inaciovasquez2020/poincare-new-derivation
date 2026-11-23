# CREEPER × REVERSE × OBVERSE: high-fan two-cycle adversarial audit

**Date:** 2026-11-23  
**Repository:** `inaciovasquez2020/poincare-new-derivation`  
**Remote branch:** `work/first-nonzero-reentry-20261027`  
**Verified remote HEAD (read-only):** `82c5513626533dd1ab925e9529264e2166bd8247`  
**Local repository / dirty status:** NOT_INSPECTED  
**Changes, commits, pushes, merges:** NONE  
**Lean compilation / axiom audit:** NOT_RUN  
**Global independent Poincaré proof:** OPEN

## RESULT

**PROVED (mathematical connected-sum argument; not Lean verified):** For every integer H there is a simplicial triangulation K of the topological 3-sphere with every vertex tetrahedral degree at least six and a genuine different-transverse two-step high-fan return whose two central edges each have tetrahedron incidence at least H. Thus simply connectedness, high edge incidence, and the absence of degree-four vertices do **not** imply exclusion of this kind of two-step return. This does **not** refute a version assuming no legal 2-3 moves or no legal strict PhiSupport descent.

**COMPUTATION_PASS:** 12 explicit connected-sum stages, with pure Python exact set and GF(2) linear-algebra verification. The finite checks include closed-triangle incidence, all vertex links (connected, 2-manifold, Euler characteristic two), return witnesses, incidence, degrees and legal 3-2 sites. Scope is finite and does not independently certify universal claims or formalize a Lean theorem.

## 1. Initial 3-spheres

Let C be the boundary complex of the cyclic 4-polytope with six vertices 0,...,5. Its tetrahedra, from Gale evenness, are:

```
0123, 0125, 0134, 0145, 0235, 0345, 1234, 1245, 2345.
```

C is a combinatorial 3-sphere; each vertex lies in six tetrahedra.

Let Q be the boundary of the four-dimensional cross-polytope, with opposite vertex pairs `(0,1)`, `(2,3)`, `(4,5)`, `(6,7)` and its 16 facets choosing one endpoint from each pair. Each vertex lies in eight tetrahedra and each edge in four tetrahedra.

Remove tetrahedron `0123` from C, remove tetrahedron `0246` from Q and identify their boundaries by

```
Q: 0→0, 2→1, 4→2, 6→3; 1→6, 3→7, 5→8, 7→9.
```

The resulting simplicial connected sum K is homeomorphic to S³, since both summands bound convex four-polytopes (and S³ # S³ ≅ S³).

## 2. Exact two-cycle and geometry

The two unordered central edges are `e0={0,2}` and `e1={1,3}`.

First fan transition, old `{0,2}`, chord `{1,3}`, transverse `5`:

```
T0-left  = 0125
T0-right = 0235
shared face = 025
```

Second fan transition, old `{1,3}`, chord `{0,2}`, transverse `4`:

```
T1-left  = 0134
T1-right = 1234
shared face = 134
```

These are adjacent pairs of link triangles at the old central edge. Both pairs have five distinct vertices as required by the source `FanChordTransition` structure. Suitable off-old-edge `witness` tetrahedra exist: `0134` for the first transition, `0125` for the second. The two transverses, 5 and 4, are unequal.

In C, each central edge has incidence three; the removed tetrahedron `0123` is incident to both. In Q, each corresponding edge has incidence four. The connected-sum rule gives `3+4−2=5` for each central edge in K. Because K is a combinatorial closed 3-manifold, their edge links are cyclic and supply the `AmbientEdgeCyclicFan` geometry; a full Lean construction of these records is **NOT_RUN**.

## 3. Exact inventory

```
f-vector (f0,f1,f2,f3): (10,33,46,23)
vertex tetrahedron degrees: (12,12,12,12,6,6,8,8,8,8)
min vertex tetrahedron degree: 6
edge incidences (02,13): (5,5)
mod-2 boundary ranks (d1,d2,d3): (9,24,22)
mod-2 Betti numbers (b0,b1,b2,b3): (1,0,0,1)
PhiSupport (repo definition): 52
legal 2-3 sites: 32
legal 3-2 sites: 4
```

The four legal 3-2 moves in the 23-tetrahedron fixture occur at edges `04`, `15`, `24`, and `35`; every one removes one of the four retained witness tetrahedra (respectively `0134`, `0125`, `1234`, and `0235`). Each legal 3-2 move produces another closed simplicial 3-manifold with PhiSupport `48` (from `52`). Thus the example fails both the *no legal 2-3 move* and the *no strict descent* hypotheses used in some fail-closed lemmas.

## 3a. Stronger adversarial fixture: a sphere with no decreasing first move

Starting from K (the 23-tetrahedron connected sum), perform two additional facet gluings with fresh copies of Q, first along `0145` and then along `2345`. Both facets lie outside the four fixed return witnesses. Each additional gluing increases by 2 the incidence of two distinct residual incidence-three edges. The final triangulation K* has:

```
f-vector (f0,f1,f2,f3): (18,69,102,51)
PhiSupport: 132
minimum vertex tetrahedron degree: 8
minimum edge incidence: 4
high return incidences (02,13): (5,5)
legal Move32 sites: 0
legal Move23 sites: 96
GF(2) boundary ranks: (17,52,50)
GF(2) Betti numbers: (1,0,0,1)
```

**COMPUTATION_PASS, exhaustive move test:** All 96 legal `2→3` moves were enumerated, applied and checked to yield a combinatorial closed 3-manifold with PhiSupport **136**. All 51 possible `1→4` stellar subdivisions were independently applied and checked, each yielding PhiSupport **140**. With no incidence-three edges and no degree-four vertices, no legal `3→2` or `4→1` move exists. Therefore **no legal single Pachner move from K* strictly decreases PhiSupport**, although K* is homeomorphic to S³ and its different-transverse high-fan return persists.

**PROVED (short combinatorial argument; not Lean):** Every legal single Pachner move in K* fails to decrease PhiSupport. The two decreasing move types are absent by the degree bounds; the remaining two move types raise tetrahedral vertex-degree defects by +4 and +8, respectively, because all original vertex degrees are at least eight. This is a counterexample to *single-move monotone descent*, not to finite descent sequences that permit temporary increases. In particular, K* still has 96 legal `2→3` exits, so it does not satisfy a no-Move23 hypothesis.

## 4. CREEPER: unbounded edge-incidence inflation

At step n≥1, perform another connected sum with Q along any tetrahedron incident to the targeted central edge but not one of the four witness tetrahedra. Initially use `0123`, which hits both central edges. For subsequent steps alternate e0 and e1.

Every sum with Q:

* adds 4 vertices and 14 tetrahedra;
* increases incidence of each old edge contained in the gluing facet by 2;
* increases tetrahedron degree of each glued old vertex by 6;
* leaves all other old vertex degrees unchanged, and introduces four vertices of tetrahedron degree 8;
* preserves S³ topology and the four witness tetrahedra.

For any central edge of incidence at least five, at most two of its incident tetrahedra are in the fixed witness set. Therefore a safe gluing facet always exists. Both central-edge incidences grow without bound by alternation. The minimum vertex degree remains six. The resulting family has

```
f-vector after n joins = (6+4n, 15+18n, 18+28n, 9+14n)
PhiSupport = 12+40n
```

For 12 joins, the exact test yielded `(f0,f1,f2,f3)=(54,231,354,177)` and central-edge incidences `(17,15)`. This gives an explicit inductive counterexample family, not merely numerical extrapolation.

## 5. BACKTRACK / REVERSE / OBVERSE: effect on proof obligations

1. **BACKTRACK:** Any different-transverse two-cycle exclusion must use hypotheses beyond simple connectedness, minimum vertex degree ≥6, and arbitrarily high central-edge incidence. The missing feature is a usable *move/gradient obstruction*, not a larger fixed incidence bound.
2. **REVERSE:** Legal 3-2 moves in the smallest countermodel reduce PhiSupport by four and each destroys one local transition witness. The inverse move test identifies exact boundary where recurrence can be broken by descent.
3. **OBVERSE:** The graph-level recurrent edge itinerary and the topological null-homotopy of its geometric loop do not, by themselves, yield a contradiction or a legal bistellar move. The carrier-to-disk-to-Pachner comparison remains essential.
4. **CREEPER:** 12 exact expansions were checked and an induction proves arbitrarily high incidence cannot rescue the naive local rigidity lemma. A separate 51-tetrahedron fixture additionally eliminates all immediate strict potential descents while retaining legal `2→3` exits.
5. **ADVERSARIAL:** This specifically refutes the overstrong two-cycle exclusion; it does **not** refute the more constrained no-Move23/no-descent lemma. These hypotheses fail for the constructed K.
6. **LEAN:** Source-level records were inspected, but no local Lean compiler and pinned repository OLEANS were used. `LEAN_VERIFIED := NOT_RUN`.

### Weakest genuinely OPEN local lemma

Consider two different-transverse `FanChordTransition` records T0 and T1 forming a two-step return under `ClosedTriangulationCore`, linked vertex-star conditions and a simply connected topological carrier. Test the **fail-closed** version:

> Under `¬ ∃ m : Move23Site, m.LegalIn K` and absence of strict topology-preserving `PhiSupport` descent, prove that such a two-cycle is impossible, or find a countermodel preserving **all** these assumptions.

This target is strictly stronger than the now-refuted incidence-only version. It is also only a local lemma: longer recurrent cycles and the global topology-preserving descent theorem remain OPEN.

### REVERSE audit: global hNoDescent is not a move-local prohibition

The source predicate `hNoDescent` in `HighFanCommonCofaceFilling.lean` and `GlobalMove32ReentryPolygonalLoopNullHomotopyFailClosed.lean` is the negation of **any** smaller-`PhiSupport` *homeomorphic* closed-core triangulation, whether reachable by one legal Pachner move, several moves, or no exhibited move path at all. It is **not** equivalent by definition to "no legal 3-2/4-1 moves." For any known triangulation of the topological S³ with positive PhiSupport, the boundary of the 4-simplex supplies a homeomorphic PhiSupport-zero comparison, making this global `hNoDescent` false. Using that comparison to discharge `hNoDescent` for arbitrary simply connected K would rely on the already-known classical Poincaré theorem, not establish an independent derivation. In the project, the missing independent reduction must be proved without assuming that homeomorphism in advance.

This exposes a second exact obligation: distinguish **actual certified move paths** from the more permissive existential homeomorphism-to-lower-Phi proposition at every load-bearing step.

### Repo naming audit

`lean/Poincare/Triangulation.lean` defines `S3 K := normalized K`, where `normalized K := PhiSupport K = 0`. This is **not the definition of being topologically homeomorphic to S³**. All topological sphere claims in this certificate rely on the independent connected-sum construction, not this syntactic `S3` predicate.

## 6. Validation, reproducibility and source references

Exact verifier: `poincare_creeper_2cycle_audit.py` (Python standard library only).  
Receipt: `poincare_creeper_2cycle_receipt.json`.  
No remote write actions, local repo modifications, commits, pushes, merges, downloads, or deletions were performed.

Repository source paths read at exact HEAD:

* `lean/Poincare/GlobalFanChordTransition.lean` — precise `FanChordTransition` fields, same-transverse two-cycle theorem.
* `lean/Poincare/GlobalFanChordEdgeProgress.lean` — high-fan states and recurrent transition paths.
* `lean/Poincare/HighFanCommonCofaceFilling.lean` — geometric loops and common-coface fillings.
* `lean/Poincare/GlobalDegreeFourDescent.lean` — certified degree-four descent fork.
* `lean/Poincare/Moves.lean` — `Move23Site.LegalIn` definition.
* `lean/Poincare/Triangulation.lean` — `PhiSupport`, `normalized`, `S3` definitions.
* `docs/certificates/high_fan_2026-11-22/CHECKPOINT.md` — previous bounded C(6,4) experiment and open different-transverse high-incidence case.

Mathematical background: boundaries of simplicial convex polytopes are simplicial spheres; simplicial connected sum along removed facets preserves combinatorial manifold structure, and S³ # S³ ≅ S³. The topology is not inferred merely from calculated mod-2 homology.

## NEXT_ACTIONS

1. Use the pinned project Lean toolchain on the Mac to instantiate the 23- and 51-tetrahedron fixtures and check `ClosedTriangulationCore`, vertex degrees, incidence and retained witness adjacency **without sorry, axioms or native_decide**.
2. Construct the two complete `FanChordTransition` instances and prove that the high-incidence different-transverse two-cycle exists; audit `#print axioms`.
3. Formalize the four local legal `Move32Site` alternatives and their `PhiSupport` decrease, verifying how the witness is destroyed.
4. Attack the narrowed fail-closed two-cycle theorem retaining the exact `hNoMove23`/`hNoDescent` assumptions, with any counterexample subjected to all assumptions.
5. Only after this local case is resolved, return to longer cycles and the disk-to-bistellar descent bridge. Do not promote the current result as an independent Poincaré proof.
