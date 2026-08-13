import Poincare.GlobalMove32SelfReentryNoDegreeFour
import Poincare.GlobalMove32WitnessedSourceFaceReentry

namespace Poincare

/--
In the globally no-degree-four branch, consider a witnessed source-face
reentry `prev → ret`.  If the returned shared edge is the anchor shared edge
up to reversal, then the predecessor source face cannot have the same
unordered vertex support as the anchor source face.

Indeed, under equality of those source-face supports, the two represented
tetrahedra remembered by the witnessed reentry would contain the anchor
source face together with the two returned-edge endpoints.  Since the
returned edge is the anchor edge, these are precisely representatives of
the two forbidden anchor Move32 source tetrahedra.
-/
theorem
    ClosedTriangulationCore.not_predecessor_sourceFace_support_eq_anchor_of_witnessedReentry_return_edge_of_no_degree_four
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
    (hstep :
      Move32SourceFaceWitnessedReentry
        K prev ret)
    (hreturn :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d)) :
    ¬ (∀ z : Nat,
      z ∈ [prev.a, prev.b, prev.c] ↔
      z ∈ [anchor.a, anchor.b, anchor.c]) := by
  intro hsource

  rcases hstep with
    ⟨tau, rho, x, y, sigma,
      htauK,
      hrhoK,
      hne,
      hprevATau,
      hprevBTau,
      hprevCTau,
      hprevARho,
      hprevBRho,
      hprevCRho,
      hxTau,
      hxPrevABC,
      hyRho,
      hyPrevABC,
      hxy,
      hsigmaK,
      hxSigma,
      hySigma,
      hnonself,
      hretD,
      hretE,
      hretRealized,
      hretThree,
      hgamma⟩

  have hanchorFaceTau :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] →
        z ∈ tau.verts := by
    intro z hzAnchor
    have hzPrev :
        z ∈ [prev.a, prev.b, prev.c] :=
      (hsource z).2 hzAnchor
    simp at hzPrev
    rcases hzPrev with hza | hzb | hzc
    · subst z
      exact hprevATau
    · subst z
      exact hprevBTau
    · subst z
      exact hprevCTau

  have hanchorFaceRho :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] →
        z ∈ rho.verts := by
    intro z hzAnchor
    have hzPrev :
        z ∈ [prev.a, prev.b, prev.c] :=
      (hsource z).2 hzAnchor
    simp at hzPrev
    rcases hzPrev with hza | hzb | hzc
    · subst z
      exact hprevARho
    · subst z
      exact hprevBRho
    · subst z
      exact hprevCRho

  have hxAnchorABC :
      x ∉ [anchor.a, anchor.b, anchor.c] := by
    intro hxAnchor
    exact hxPrevABC ((hsource x).2 hxAnchor)

  have hyAnchorABC :
      y ∉ [anchor.a, anchor.b, anchor.c] := by
    intro hyAnchor
    exact hyPrevABC ((hsource y).2 hyAnchor)

  have hself :
      (x = anchor.d ∧ y = anchor.e) ∨
      (x = anchor.e ∧ y = anchor.d) := by
    rcases hreturn with hdirect | hreverse

    · exact Or.inl
        ⟨hretD.symm.trans hdirect.1,
         hretE.symm.trans hdirect.2⟩

    · exact Or.inr
        ⟨hretD.symm.trans hreverse.1,
         hretE.symm.trans hreverse.2⟩

  exact
    hcore.not_move32_complementEdge_self_reentry_of_no_degree_four
      hlinks
      hconn
      hNoFour
      anchor
      hanchorRealized
      htauK
      hrhoK
      hne
      (hanchorFaceTau anchor.a (by simp))
      (hanchorFaceTau anchor.b (by simp))
      (hanchorFaceTau anchor.c (by simp))
      (hanchorFaceRho anchor.a (by simp))
      (hanchorFaceRho anchor.b (by simp))
      (hanchorFaceRho anchor.c (by simp))
      hxTau
      hxAnchorABC
      hyRho
      hyAnchorABC
      hself

end Poincare
