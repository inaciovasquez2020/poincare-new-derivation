import Poincare.GlobalMove32ReentryTwoSidedCarrierEscape
import Mathlib.Tactic

namespace Poincare

/--
A witnessed incidence-three return to a repeated supported-edge state cannot
simultaneously preserve both the anchor-to-return five-vertex carrier support
and the predecessor-to-return five-vertex carrier support.

This is a finite-transition obstruction only.  It does not assert that a
sequence of changing carriers is acyclic.
-/
theorem
    ClosedTriangulationCore.anchor_return_carrier_support_ne_or_predecessor_return_carrier_support_ne_of_witnessedReentry_return_state_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn :
      TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (anchor prev ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorThree : anchor.SharedEdgeExactlyThree K)
    (hprevRealized : prev.RealizedIn K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    (hstep :
      Move32SourceFaceWitnessedReentry
        K
        prev
        ret)
    (hstate :
      sharedSupportedEdgeState
          hcore
          anchor
          hanchorRealized =
        sharedSupportedEdgeState
          hcore
          ret
          hretRealized) :
    ¬ (
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ↔
          z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e]) ∨
    ¬ (
      ∀ z : Nat,
        z ∈ [prev.a, prev.b, prev.c, prev.d, prev.e] ↔
          z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e]) := by

  rcases
      hcore.exists_return_sourceFace_vertex_outside_anchor_carrier_or_predecessor_sourceFace_vertex_outside_return_carrier_of_witnessedReentry_return_state_of_no_degree_four
        hlinks
        hconn
        hNoFour
        anchor
        prev
        ret
        hanchorRealized
        hanchorThree
        hprevRealized
        hretRealized
        hretThree
        hstep
        hstate with
    hreturnEscape | hpredecessorEscape

  · left
    intro hcarrier

    rcases hreturnEscape with
      ⟨q, hqReturnSource, hqOutsideAnchor⟩

    have hqReturnCarrier :
        q ∈ [ret.a, ret.b, ret.c, ret.d, ret.e] := by
      simp at hqReturnSource ⊢
      tauto

    exact
      hqOutsideAnchor
        ((hcarrier q).2 hqReturnCarrier)

  · right
    intro hcarrier

    rcases hpredecessorEscape with
      ⟨z, hzPredecessorSource, hzOutsideReturn⟩

    have hzPredecessorCarrier :
        z ∈ [prev.a, prev.b, prev.c, prev.d, prev.e] := by
      simp at hzPredecessorSource ⊢
      tauto

    exact
      hzOutsideReturn
        ((hcarrier z).1 hzPredecessorCarrier)

end Poincare
