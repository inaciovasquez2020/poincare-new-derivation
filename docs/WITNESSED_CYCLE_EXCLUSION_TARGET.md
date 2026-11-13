# Witnessed-cycle exclusion target

Status: **TARGET ONLY — not proved; no Lean theorem closure claimed.**

## Purpose

The missing result is global exclusion of a closed trajectory of the *full*
mixed fan/reentry state, not merely recurrence of its finite key. The state
must retain the HighFanState transition data or the full WitnessedReentryState
site/realization/exact-three data. The existing FanReentryModeStep is the
lineage-preserving transition relation.

Relevant existing results:

- ClosedTriangulationCore.exists_perpetual_fanReentryMode_trajectory_of_noMove23_noDescent
  constructs an infinite linked trajectory under the no-Move23/no-descent
  assumptions.
- exists_recurrent_fanReentryModeKey_classified gives a repeated *coarse key*,
  classified into a nonconsecutive fan return or a reentry return.
- Neither result excludes a cycle of complete states.

## Exact mathematical target

For a fixed triangulation K, suppose:

1. ClosedTriangulationCore K;
2. the represented triangulation realizes a closed, connected topological
   three-manifold;
3. every represented vertex link is connected;
4. no represented vertex has degree four;
5. no legal Move23 exists in K;
6. no strictly smaller PhiSupport triangulation with the same topological
   geometric carrier exists;
7. no nonself high-edge escape exists in the applicable source-face
   obstruction branch.

Then prove that there is no positive period p and no complete-state sequence
states : Nat → FanReentryModeState K such that

    (∀ n, FanReentryModeStep K (states n) (states (n + 1))) ∧
    (∀ n, states (n + p) = states n)

The intended theorem shape is:

    theorem no_periodic_full_fanReentryMode_trajectory
        (hcore : ClosedTriangulationCore K)
        (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
        (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
        (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
        (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
        (hNoDescent : NoTopologyPreservingPhiSupportDescent K)
        (hNoHigh : NoNonselfHighEdgeEscape K)
        (states : Nat → FanReentryModeState K)
        (hstep : ∀ n, FanReentryModeStep K (states n) (states (n + 1)))
        (p : Nat) (hp : 0 < p)
        (hperiod : ∀ n, states (n + p) = states n) :
        False

NoTopologyPreservingPhiSupportDescent and NoNonselfHighEdgeEscape above are
descriptive names for the existing quantified hypotheses, not currently
declared Lean constants. The snippet is a theorem contract, not compilable Lean
source.

## Proof obligations that must be discharged

A valid proof must derive at least one of these from the existing hypotheses
and the actual transition witnesses:

- a legal Move23;
- a strict topology-preserving PhiSupport descent;
- a prohibited high-edge escape or degree-four vertex;
- a contradiction in the global tetrahedral/vertex-link incidence data of
  the entire closed trajectory.

It is not sufficient to cite finite recurrence, equality of coarse edge keys,
or the three separate exact-three star normal forms. It is also not sufficient
to postulate a decreasing measure or add an axiom.

## Critical verification boundary

This target may be false under the current hypotheses. Before attempting to
prove it in Lean, test whether a finite triangulation satisfying all stated
geometric hypotheses can support a periodic full-state trajectory. If a
counterexample exists, identify which hypothesis or transition rule must be
strengthened. Do not add sorry, admit, an axiom, or an opaque surrogate theorem
to make the target appear closed.

**Current status:** the target is formulated; its truth and proof remain open.
