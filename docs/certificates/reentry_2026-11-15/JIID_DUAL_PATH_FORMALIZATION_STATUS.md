# JIID — dual-path nonboundary formalization boundary

**Date:** 2026-11-15. **Status:** abstract finite dual-path parity theorems **LEAN_VERIFIED** on the audit branch at commit `c4f1307d6690620df9586ee1d033ca58b250dd35` (GitHub Actions run `43766201620`); abstract dual-cell edit parity theorems **LEAN_VERIFIED** at the same commit (run `43766201604`). No global JIID closure.

## Candidate source

`DualPathNonboundaryParity.lean` defines a face-to-two-tetrahedra incidence model with Boolean mod-two 3-boundary, the face-avoiding dual-adjacency relation, and the following **Lean-verified abstract** theorems:

- `Poincare.DualPathParity.equal_on_avoiding_path`
- `Poincare.DualPathParity.nonboundary_of_avoiding_return`

The general proof is by induction on `Relation.ReflTransGen`: if an edge in the dual path crosses a face absent from `sphere`, its two tetrahedral coefficients must agree. The marked face in the sphere forces them to disagree. Boolean xor is the coefficient addition in F₂.

**Not yet integrated into the actual triangulation:** The abstract face-pair map requires a proof that every source triangle has exactly two represented incident tetrahedra and is correctly identified by `ClosedTriangulationCore`; `s.RealizedIn K` and link connectivity then give the avoiding dual path. This bridge has not been formalized.

## Non-circular proposed integration

1. Instantiate the face-pair model using actual `Tet` and canonical represented triangular faces, deriving exactly-two incidence from `ClosedTriangulationCore`.
2. Define `S_q` on the represented face type and prove its four faces are represented; show q exists using the `hnonself` field in `Move32SourceFaceWitnessedReentry`.
3. Construct an avoiding dual path from `abcx` to a tetrahedron containing `xy` by `VertexLinkConnected K x`, and onward to `abcy` by `VertexLinkConnected K y`.
4. Apply `nonboundary_of_avoiding_return`, obtaining `S_q ∉ range(∂₃)`.
5. Prove the independent **topological bridge**:
   closed connected topological 3-manifold + `TriangulationRealizationSimplyConnected K` + a compatible genuine triangulation ⇒ every mod-two simplicial 2-cycle is a 3-boundary. This requires geometric/simplicial homology compatibility and mod-two Poincaré duality (or a direct simple-connected sphere-separation theorem). It must **not** assume S³ recognition or the target JIID descent.
6. Deduce the contradiction and eliminate the `reentry_next` constructor under simple connectedness. High-fan cycles still OPEN.

## Why the bridge is substantive

SimplyConnectedSpace in current Mathlib is a **path-homotopy** property. Merely asserting `H₂=0` from it requires either formalizing the relevant homology comparisons and duality or a genuine Jordan-type separation result; finite search and graph parity do not supply it. The existing repository proves specific `VertexLinkMod2...` chain results and a fixed-12-vertex cocycle theorem, not this global bridge.

## Verified versus unverified

- Independent mathematical finite parity proof: **PROVED**.
- Python dual graph / F₂ test of 51-tetrahedron witness, as previously recorded: **COMPUTATION_PASS** (existing receipt; no rerun in this phase).
- Lean kernel compilation: **PASS** for `lean/Poincare/DualPathNonboundaryParity.lean`, exact commit `c4f1307d6690620df9586ee1d033ca58b250dd35`, CI run `43766201620`.
- Abstract dual-cell edit parity: **PASS** for `research/candidates/DualCellParityRelationsIsolated.lean`, same commit, CI run `43766201604`.
- `#print axioms`: **PASS** in both dedicated workflows; allowed axioms restricted to `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. These are not proofs of the geometric comparison.
- Global triangulation and topological bridges: **OPEN**.
- JIID/global independent Poincaré derivation: **OPEN**.
- GitHub preservation: **COMMITTED** on `audit/reentry-adversarial-h1-20261115`; finite parity is integrated into `lean/Poincare/` but the dual-cell module remains an isolated candidate. Neither constructs the actual incidence/dual-CW carrier comparison. Merge is a separate gate.
