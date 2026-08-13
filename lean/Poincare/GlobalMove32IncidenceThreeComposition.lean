import Poincare.GlobalMove32IncidenceThreeCandidate
import Poincare.GlobalMove32IncidenceThreeSplit

namespace Poincare

/--
An ambient edge of incidence exactly three produces either a genuine
topology-preserving strict `PhiSupport` descent or a realized Move32 site
whose source face is already present.

This is the direct composition of the certified incidence-three candidate
constructor with the certified legality/source-face split.
-/
theorem
    ClosedTriangulationCore.exists_descent_or_realized_sourceFace_obstruction_of_edgeIncidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (d e : Nat)
    (hde : d ≠ e)
    (hthree :
      (K.tets.filter
        (fun τ =>
          decide
            (d ∈ τ.verts ∧
             e ∈ τ.verts))).length = 3) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    ∃ s : Move32Site,
      s.d = d ∧
      s.e = e ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      ∃ τ ∈ K.tets,
        s.a ∈ τ.verts ∧
        s.b ∈ τ.verts ∧
        s.c ∈ τ.verts := by

  obtain ⟨s, hsd, hse, hrealized, hthreeS⟩ :=
    hcore.exists_move32Site_realizedIn_of_edgeIncidence_three
      d e hde hthree

  rcases
      exists_closedCore_homeomorphic_PhiSupport_lt_or_sourceFace_obstruction_of_move32_incidence_three
        hcore hNoFour s hrealized hthreeS with
    hdescent | hobstruction

  · exact Or.inl hdescent

  · exact
      Or.inr
        ⟨s,
          hsd,
          hse,
          hrealized,
          hthreeS,
          hobstruction⟩

end Poincare
