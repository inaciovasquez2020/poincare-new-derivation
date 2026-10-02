import Poincare.GlobalMove32ReentryPolygonalLoopFailClosed
import Poincare.GlobalMove32ReentryPolygonalLoopNullHomotopy

namespace Poincare

/--
Under explicit exclusion of strict topological `PhiSupport` descent and
nonself complementary high-incidence escape, the initial exact-three Move32
source-face obstruction produces the existing ordered recurrence-driven
polygonal-loop certificate together with the full relative null-homotopy
square supplied by simple connectivity.

This is a composition theorem only.  It does not assert that the recurrent
polygonal loop is homotopically nontrivial or that its null-homotopy forces a
combinatorial contradiction.
-/
theorem ClosedTriangulationCore.exists_polygonalLoop_nullHomotopyData_of_no_other_sourceFace_outcome
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
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
    (start : Move32Site)
    (hstartRealized : start.RealizedIn K)
    (hstartThree : start.SharedEdgeExactlyThree K)
    (hstartObstruction :
      ∃ tau ∈ K.tets,
        start.a ∈ tau.verts ∧
        start.b ∈ tau.verts ∧
        start.c ∈ tau.verts) :
    ∃ p : WitnessedReentryPolygonalLoopCertificate K,
      Nonempty
        (CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop) := by
  obtain ⟨p⟩ :=
    hcore.exists_polygonalLoopCertificate_of_no_other_sourceFace_outcome
      hlinks
      hconn
      hSC
      hNoFour
      hNoDescent
      hNoHigh
      start
      hstartRealized
      hstartThree
      hstartObstruction

  exact ⟨p, p.exists_nullHomotopyData hSC⟩

end Poincare
