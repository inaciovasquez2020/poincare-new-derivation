import Poincare.GlobalMove32IncidenceThreeComposition
import Poincare.GlobalMove32SourceFaceLegalMove23High

namespace Poincare

/-- Under exclusion of strict topology-preserving descent and nonself
high-edge escape, every exact-incidence-three represented edge is forced into
a realized Move32 source-face obstruction followed by a witnessed reentry. -/
theorem
    ClosedTriangulationCore.exists_witnessedReentry_of_edgeIncidence_three_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
          x ≠ y ∧
          sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧
          y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (x ∈ gamma.verts ∧
                   y ∈ gamma.verts))).length)
    (d e : Nat)
    (hde : d ≠ e)
    (hthree :
      (K.tets.filter
        (fun tau =>
          decide
            (d ∈ tau.verts ∧
             e ∈ tau.verts))).length = 3) :
    ∃ s s' : Move32Site,
      s.d = d ∧
      s.e = e ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K s s' := by
  rcases
      hcore.exists_descent_or_realized_sourceFace_obstruction_of_edgeIncidence_three
        hNoFour d e hde hthree with
    hdesc | hsource

  · exact (hNoDescent hdesc).elim

  · rcases hsource with
      ⟨s, hsd, hse, hrealized, hthreeS, hobstruction⟩

    rcases
        hcore.exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
          hlinks hconn hNoFour s hrealized hobstruction with
      hdesc | hhigh | hreentry

    · exact (hNoDescent hdesc).elim

    · exact (hNoHigh s hrealized hobstruction hhigh).elim

    · rcases hreentry with ⟨s', hrel⟩
      exact ⟨s, s', hsd, hse, hrealized, hthreeS, hrel⟩

end Poincare
