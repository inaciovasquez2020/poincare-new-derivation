import Poincare.GlobalMove32ReentryPredecessorCarrierEscape
import Poincare.GlobalMove32ReentryReturnUnlabeledConfiguration

namespace Poincare

/--
If a witnessed reentry returns to the same supported-edge state and the return
source face has the same unlabeled support as the anchor source face, then the
predecessor source face contains a vertex outside the complete five-vertex
carrier of the return site.

This is only a local carrier-separation statement.  It does not assert
acyclicity or termination.
-/
theorem
    ClosedTriangulationCore.exists_predecessor_sourceFace_vertex_outside_return_carrier_of_witnessedReentry_same_source_return_state_of_no_degree_four
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
    (hsource :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
          z ∈ [ret.a, ret.b, ret.c])
    (hstate :
      sharedSupportedEdgeState
          hcore
          anchor
          hanchorRealized =
        sharedSupportedEdgeState
          hcore
          ret
          hretRealized) :
    ∃ z ∈ [prev.a, prev.b, prev.c],
      z ∉ [ret.a, ret.b, ret.c, ret.d, ret.e] := by
  have hconfig :=
    hcore.unlabeledConfiguration_eq_of_sourceFace_support_eq_of_sharedSupportedEdgeState_eq
      anchor
      ret
      hanchorRealized
      hanchorThree
      hretRealized
      hretThree
      hsource
      hstate

  have hedge :
      (ret.d = anchor.d ∧
        ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧
        ret.e = anchor.d) := by
    rcases hconfig.1 with hdirect | hreverse
    · exact
        Or.inl
          ⟨hdirect.1.symm,
            hdirect.2.symm⟩
    · exact
        Or.inr
          ⟨hreverse.2.symm,
            hreverse.1.symm⟩

  have hcarrier :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ↔
          z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e] :=
    hconfig.2.1

  obtain ⟨z, hzPrev, hzOutsideAnchor⟩ :=
    hcore.exists_predecessor_sourceFace_vertex_outside_anchor_carrier_of_witnessedReentry_return_edge_of_no_degree_four
      hlinks
      hconn
      hNoFour
      anchor
      prev
      ret
      hanchorRealized
      hprevRealized
      hstep
      hedge

  refine ⟨z, hzPrev, ?_⟩

  intro hzReturnCarrier

  exact
    hzOutsideAnchor
      ((hcarrier z).2 hzReturnCarrier)

end Poincare
