# Xgate cyclic-rigidity frontier

Status: **OPEN — no repository theorem closure claimed.**

Base inspected: `bc377ea27d02c5d23e70f6e07f6000eb4322c1b3`.

## Existing verified inputs

- `Poincare.exists_recurrent_highFanEdgeEndpoints` gives indices `i,j` with `i + 1 < j`, a finite bound by `Fintype.card (SupportedEdgeState K)`, return of the same *unordered central edge* (possibly with reversed endpoint order), and retained transition-step facts on the segment.
- `Poincare.EXISTS_RECURRENT_LOCAL_FAN_CONFIGURATION` is stronger than the endpoint recurrence alone: since `HighFanLocation K` is finite and consecutive locations cannot coincide, it obtains a nonconsecutive repeated **oriented** central edge together with the same retained ordered adjacent link-triangle pair.
- `Poincare.FanChordTransition.same_location_transverse_eq` proves that repeated retained local location forces the same transverse carrier.
- `Poincare.FanChordTransition.same_location_same_transverse_same_chord` proves that the same location and transverse carrier determine both chord endpoints.
- `Poincare.repeated_highFan_location_next_edgeState_eq` combines these facts: repeated retained local location forces equality of the successor edge states.
- `Poincare.FanChordTransition.same_location_different_transverse_impossible` rules out different transverse carriers at the same retained location.
- `Poincare.ClosedTriangulationCore.fanChord_twoCycle_same_transverse_impossible_noFour` excludes the specific two-step return with the same transverse carrier under the no-degree-four and connected-link hypotheses.
- `Poincare.ClosedTriangulationCore.exists_finite_recurrent_highFanEdgeCycle_of_noMove23_noDescent_noHigh` constructs a recurrent segment from the stated no-move, no-descent, and no-high-edge exclusions. Its documentation explicitly says that this does not itself assert the recurrent cycle is impossible.

## What has been derived

The changing-transverse case at an identical retained location is already excluded. In fact, a repeated `HighFanLocation` forces the transverse carriers and chord endpoints to agree, so the next central edge state repeats as well. This is the repository's existing local shortening mechanism.

That still does **not** contradict the current recurrent-cycle theorem. The exact implication proved by `repeated_highFan_location_next_edgeState_eq` is only\n\n`states[i].location = states[j].location` and valid continuation steps imply `states[i+1].edgeState = states[j+1].edgeState`.\n\nIt does **not** prove `states[i+1] = states[j+1]`, equality of their retained `FanChordTransition`s, or equality of their next local locations. `HighFanState` stores a transition, including the ordered adjacent link triangles and tetrahedral witnesses; equality of the canonical central-edge key forgets that data. The continuation construction is existential rather than a demonstrated function of the edge state, so the same central edge can carry different retained transition data.\n\nA proposed shortening based only on successor-edge equality is therefore invalid: the repeated edge-state indices are shifted by one but have the same separation, and no repeated full state or well-founded decrease follows. To make shortening valid, one needs either (a) a deterministic/memoryless continuation theorem that is proved compatible with the geometric construction and a cycle-minimality argument, or (b) a separate incidence/link invariant that forbids the residual cycle. Neither follows merely from finite recurrence of edge states.

## Abstract countermodel boundary

At the abstract finite-state level, a directed cycle can return to an edge key while retaining different transition/location labels at each occurrence. This shows that the endpoint bookkeeping alone cannot imply geometric rigidity. It is **not** a triangulation of a closed 3-manifold and is **not** a counterexample to the repository's full geometric hypotheses. No topology-compliant counterexample has been found or claimed.

## Weakest missing invariant

The prior proposed target—forcing a repeated location with different transverse carriers—is the wrong target because the existing lemmas prove that case impossible directly. The useful target is instead one of the following:

1. **Cycle-shortening invariant:** show that the repeated-location successor-edge equality produces a strictly shorter recurrent object in a well-founded measure that the actual construction preserves; or
2. **Geometric closure invariant:** show that any recurrent edge cycle with changing retained locations necessarily produces the already excluded same-transverse two-step configuration, or a legal Move23 / strict topology-preserving `PhiSupport` descent / prohibited high-edge obstruction.

The invariant must be derived from the retained transition geometry and the actual `ClosedTriangulationCore`, manifold, connected-link, no-degree-four, no-Move23, no-descent, and no-high-edge assumptions. It must not be introduced as an unproved axiom or assumed theorem.

## Verification boundary

- **Proved at base:** finite recurrent edge endpoint reduction; finite repeated-local-location reduction; uniqueness of transverse carrier and chord endpoints at a repeated location; equality of successor edge states; the same-transverse two-step contradiction.
- **Not proved:** a well-founded cycle-shortening invariant; cyclic rigidity for longer cycles with changing retained locations; a topology-compliant counterexample; global high-fan termination; `Poincare.JIID`; Poincare conjecture.
- **Changes in this branch:** this frontier record only; no Lean theorem is asserted by this document.
