import Poincare.GlobalMove32ReentryReturnCrossingConfiguration
import Poincare.GlobalMove32ReentryReturnSourceFaceCarrierEscape
import Poincare.GlobalMove32ReentrySameSourcePredecessorCarrierEscape

namespace Poincare

/--
At a witnessed incidence-three return to the same supported-edge state in the
no-degree-four branch, carrier escape occurs on one of the two sides.

Either the return source face contains a vertex outside the anchor five-vertex
carrier, or the predecessor source face contains a vertex outside the return
five-vertex carrier.

This is a local recurrence obstruction only.  It does not assert acyclicity or
termination through a sequence of changing carriers.
-/
theorem
    ClosedTriangulationCore.exists_return_sourceFace_vertex_outside_anchor_carrier_or_predecessor_sourceFace_vertex_outside_return_carrier_of_witnessedReentry_return_state_of_no_degree_four
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
    (∃ q ∈ [ret.a, ret.b, ret.c],
      q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e]) ∨
    (∃ z ∈ [prev.a, prev.b, prev.c],
      z ∉ [ret.a, ret.b, ret.c, ret.d, ret.e]) := by

  obtain
    ⟨tau,
      rho,
      sigma,
      htauK,
      hrhoK,
      hsigmaK,
      hTauRho,
      hprevATau,
      hprevBTau,
      hprevCTau,
      hprevARho,
      hprevBRho,
      hprevCRho,
      hretDTau,
      hretERho,
      hretDSigma,
      hretESigma,
      hretENotTau,
      hretDNotRho,
      hSigmaTau,
      hSigmaRho,
      hreturnEdge,
      hanchorTarget⟩ :=
    hcore.exists_witnessedReentry_return_crossing_anchor_target_of_sharedSupportedEdgeState_eq
      anchor
      prev
      ret
      hanchorRealized
      hanchorThree
      hprevRealized
      hretRealized
      hstep
      hstate

  have hbranch :=
    hcore.sourceFace_support_eq_or_distinct_third_vertex_outside_anchor_carrier_of_return_target
      anchor
      ret
      hanchorRealized
      hretRealized
      hretThree
      hsigmaK
      hretDSigma
      hretESigma
      hreturnEdge
      hanchorTarget

  rcases hbranch with hsame | hdistinct

  · right

    exact
      hcore.exists_predecessor_sourceFace_vertex_outside_return_carrier_of_witnessedReentry_same_source_return_state_of_no_degree_four
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
        hsame
        hstate

  · left

    rcases hdistinct with
      ⟨u,
        v,
        p,
        q,
        huv,
        hpu,
        hpv,
        hqu,
        hqv,
        hpAnchor,
        hqRet,
        hanchorExact,
        hretExact,
        hpq,
        hqOutside⟩

    exact
      ⟨q,
        hqRet,
        hqOutside⟩

end Poincare
