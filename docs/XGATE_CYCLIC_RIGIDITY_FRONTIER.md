# Xgate cyclic-rigidity frontier

Status: **OPEN — no repository theorem closure claimed.**

Base inspected: `bc377ea27d02c5d23e70f6e07f6000eb4322c1b3`.

## Existing verified inputs

- `Poincare.exists_recurrent_highFanEdgeEndpoints` gives indices `i,j` with `i + 1 < j`, a finite bound by `Fintype.card (SupportedEdgeState K)`, return of the same *unordered central edge* (possibly with reversed endpoint order), and retained transition-step facts on the segment.
- `FanChordTransition.same_location_different_transverse_impossible` excludes two transitions with the same retained adjacent link triangles and different transverse vertices, for a fixed oriented central edge.
- `ClosedTriangulationCore.fanChord_twoCycle_same_transverse_impossible_noFour` excludes the specific two-step return with the same transverse carrier under the no-degree-four and connected-link hypotheses.
- `ClosedTriangulationCore.exists_finite_recurrent_highFanEdgeCycle_of_noMove23_noDescent_noHigh` constructs the recurrent segment from the stated no-move, no-descent, and no-high-edge exclusions. Its own documentation explicitly says it does not assert that the recurrent cycle is impossible.

## Target obligation

The missing result is not finite recurrence. It is a geometric rigidity statement that connects recurrence of an unordered edge to the transition's richer data.

A candidate target, to be formalized with explicit orientation transports, is:

> For every recurrent segment satisfying the exact existing hypotheses, either (a) two transitions based at the same identified oriented central edge have the same ordered adjacent link-triangle location but different transverse vertices, or (b) the segment contains the existing same-transverse two-step return.

Together with the existing local contradiction lemmas, that target would eliminate the recurrent segment. **This target is not proved by the endpoint theorem.**

## Why the endpoint theorem alone is insufficient

The endpoint theorem records only recurrence of an unordered edge, transition continuation, and inequality of consecutive edge states. Those data do not encode a repeated adjacent-link location or a two-step return.

At the abstract finite-state level, a directed 3-cycle can return to its starting edge state, change state at each step, and assign three distinct local-location labels and three distinct transverse labels. This is a countermodel to the implication from the endpoint bookkeeping *alone*. It is **not** a triangulation of a closed 3-manifold and is **not** a counterexample to the repository's full geometric hypotheses.

Therefore, a proof must use additional geometric incidence/link constraints beyond the currently stated recurrence conclusion. No topology-compliant counterexample has been found or claimed.

## Weakest missing invariant to investigate

Prove a cycle-wide incidence/link invariant that forces at least one of the following:

1. a repeated, orientation-aligned adjacent pair of link triangles at the same central edge, allowing `same_location_different_transverse_impossible` to apply; or
2. a two-step return with matching transverse carrier, allowing `fanChord_twoCycle_same_transverse_impossible_noFour` to apply.

The invariant must be derived from the retained transition geometry and the actual `ClosedTriangulationCore`, manifold, connected-link, no-degree-four, no-Move23, no-descent, and no-high-edge assumptions. It must not be introduced as an unproved axiom or assumed theorem.

## Verification boundary

- **Proved at base:** finite recurrent edge endpoint reduction and the two local exclusion lemmas above.
- **Not proved:** cyclic rigidity for longer cycles; a topology-compliant counterexample to cyclic rigidity; global high-fan termination; `Poincare.JIID`; Poincare conjecture.
- **Repository changes in this branch:** this frontier record only; no Lean theorem is asserted by this document.
