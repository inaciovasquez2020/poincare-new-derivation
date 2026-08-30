import Poincare.GlobalMove32ReentryFirstNonzeroIncidenceThreeCandidate
import Poincare.GlobalMove32IncidenceThreeSplit

namespace Poincare

/-- In the no-degree-four branch, the exact-incidence-three half of a
one-sided refined-ear cross edge already yields either strict topological
`PhiSupport` descent or an explicit represented source face for the newly
constructed Move32 candidate on that cross edge. -/
theorem ClosedTriangulationCore.exists_descent_or_sourceFace_obstruction_of_firstEar_crossEdge_incidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
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
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts := by
  obtain ⟨s, hsd, hse, hrealized, hthreeS⟩ :=
    hcore.exists_move32Site_realizedIn_of_firstEar_crossEdge_incidence_three
      anchor hanchorRealized v x hcross hthree

  rcases
      exists_closedCore_homeomorphic_PhiSupport_lt_or_sourceFace_obstruction_of_move32_incidence_three
        hcore hNoFour s hrealized hthreeS with
    hdescent | hobstruction

  · exact Or.inl hdescent
  · exact Or.inr ⟨s, hsd, hse, hrealized, hthreeS, hobstruction⟩

end Poincare
