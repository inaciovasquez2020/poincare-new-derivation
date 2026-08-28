import Poincare.GlobalMove32ReentryFirstNonzeroIncidenceThreeDescentFork
import Poincare.GlobalMove32WitnessedSourceFaceReentry

namespace Poincare

/-- In the no-degree-four branch, an exact-incidence-three first-ear cross
edge either gives strict topological `PhiSupport` descent immediately, or the
resulting realized exact-three Move32 candidate's represented source face is
fed into the existing witnessed-reentry classification.  The remaining
non-descent outcomes are therefore a legal Move23 on that source face, a
nonself complementary edge of incidence at least four, or a witnessed
source-face reentry step. -/
theorem ClosedTriangulationCore.exists_descent_or_firstEar_crossEdge_sourceFace_resolution_of_incidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (anchor : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (v x : Nat)
    (hcross :
      (v = anchor.b ∧ x = anchor.d) ∨
        (v = anchor.b ∧ x = anchor.e) ∨
        (v = anchor.a ∧ x = anchor.d) ∨
        (v = anchor.a ∧ x = anchor.e))
    (hthree :
      (K.tets.filter
        (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length = 3) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    ∃ s : Move32Site,
      s.d = v ∧
      s.e = x ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      ((∃ m : Move23Site,
          m.a = s.a ∧
          m.b = s.b ∧
          m.c = s.c ∧
          m.LegalIn K) ∨
        (∃ y z sigma,
          y ≠ z ∧
          sigma ∈ K.tets ∧
          y ∈ sigma.verts ∧
          z ∈ sigma.verts ∧
          ¬ ((y = s.d ∧ z = s.e) ∨
             (y = s.e ∧ z = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (y ∈ gamma.verts ∧
                   z ∈ gamma.verts))).length) ∨
        ∃ s' : Move32Site,
          Move32SourceFaceWitnessedReentry K s s') := by

  rcases
      hcore.exists_descent_or_sourceFace_obstruction_of_firstEar_crossEdge_incidence_three
        hNoFour anchor hanchorRealized v x hcross hthree with
    hdesc | ⟨s, hsd, hse, hrealized, hthreeS, hobstruction⟩

  · exact Or.inl hdesc

  · rcases
        hcore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
          hlinks hconn hNoFour s hrealized hobstruction with
      hmove23 | hdesc | hhigh | hreentry

    · exact Or.inr ⟨s, hsd, hse, hrealized, hthreeS, Or.inl hmove23⟩
    · exact Or.inl hdesc
    · exact Or.inr ⟨s, hsd, hse, hrealized, hthreeS, Or.inr (Or.inl hhigh)⟩
    · exact Or.inr ⟨s, hsd, hse, hrealized, hthreeS, Or.inr (Or.inr hreentry)⟩

end Poincare
