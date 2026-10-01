import Poincare.GlobalMove32ReentryCarrierSupportChange

namespace Poincare

/--
VCIBT (Vertex Cyclic Invariant Branches Twist) records the two carrier
branches available at a witnessed return to a previously represented
supported-edge state.

The value is the number of the two cyclic carrier branches that fail to
preserve the returning five-vertex carrier. Thus VCIBT = 0 is the forbidden
no-twist configuration, while VCIBT > 0 records a certified branch twist.

This is a local progress invariant. It is not a termination theorem and it
does not assert Poincare.JIID.
-/
def VCIBT
    (anchor prev ret : Move32Site) : Nat :=
  (if h :
      (∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ↔
          z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e])
    then 0 else 1) +
  (if h :
      (∀ z : Nat,
        z ∈ [prev.a, prev.b, prev.c, prev.d, prev.e] ↔
          z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e])
    then 0 else 1)

/--
The VCIBT branch value is positive at every witnessed incidence-three
return to the same supported-edge state in the no-degree-four branch.

Equivalently, a return cannot preserve both cyclic five-vertex carriers:
at least one of the anchor-to-return or predecessor-to-return branches
twists.
-/
theorem vertexCyclicInvariantBranchesTwist_VCIBT
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
    0 < VCIBT anchor prev ret := by
  classical

  rcases
      hcore.anchor_return_carrier_support_ne_or_predecessor_return_carrier_support_ne_of_witnessedReentry_return_state_of_no_degree_four
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
    hanchor | hprev

  · simp [VCIBT, hanchor]
  · simp [VCIBT, hprev]

/--
The zero branch is exactly the excluded configuration. This gives the
invariant in the form needed by later well-founded measures: a repeated
supported-edge state has VCIBT ≠ 0.
-/
theorem VCIBT_ne_zero
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
    VCIBT anchor prev ret ≠ 0 := by
  exact Nat.ne_of_gt
    (vertexCyclicInvariantBranchesTwist_VCIBT
      hcore
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
      hstate)

end Poincare


namespace Poincare

/--
A VCIBT return carries two independent progress facts at once: the return
cannot preserve both carrier branches, and the witnessed reentry successor
cannot preserve the preceding canonical shared-edge state.

This is the precise finite transition package needed before attempting a
global well-founded measure. It still does not assert that the resulting
finite transition graph is acyclic.
-/
theorem VCIBT_reentry_progress
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
    0 < VCIBT anchor prev ret ∧
      sharedSupportedEdgeState
          hcore
          ret
          hretRealized ≠
        sharedSupportedEdgeState
          hcore
          prev
          hprevRealized := by
  constructor
  · exact
      vertexCyclicInvariantBranchesTwist_VCIBT
        hcore
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
        hstate
  · exact
      hcore.sharedSupportedEdgeState_ne_of_sourceFaceReentry
        prev
        ret
        hprevRealized
        hstep

end Poincare
