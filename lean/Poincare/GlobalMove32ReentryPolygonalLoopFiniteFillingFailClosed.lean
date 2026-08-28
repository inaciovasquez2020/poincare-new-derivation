import Poincare.GlobalMove32ReentryPolygonalLoopNullHomotopyFailClosed

namespace Poincare

/--
Under the explicit exclusion of the other one-step source-face outcomes, the
initial exact-three Move32 source-face obstruction produces the ordered
recurrence-driven polygonal loop, a chosen relative null-homotopy, and a
finite dyadically refined square grid whose every whole cell is carried by one
represented open vertex star.

This is the finite filling certificate already available from the existing
null-homotopy machinery.  It does not assert that the star-labelled filling
forces a Pachner exit, a strict descent, or a contradiction.
-/
theorem ClosedTriangulationCore.exists_polygonalLoop_dyadic_squareGrid_vertexStar_control_of_no_other_sourceFace_outcome
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
    (hNoMove23 :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ q : Move23Site,
          q.a = s.a ∧
          q.b = s.b ∧
          q.c = s.c ∧
          q.LegalIn K)
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
        start.c ∈ tau.verts)
    (m : Nat) :
    ∃ p : WitnessedReentryPolygonalLoopCertificate K,
      ∃ H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop,
        ∃ N : Nat, ∃ hN : 0 < N,
          ∃ hD : 0 < N * 2 ^ m,
            ∀ i j : Fin (N * 2 ^ m),
              ∃ v, v ∈ vertexSupport K ∧
                ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell
                    (N * 2 ^ m) hD i j,
                  (H.homotopy z).1 ∈
                    triangulationTopologicalVertexStar K v := by
  obtain ⟨p, hH⟩ :=
    hcore.exists_polygonalLoop_nullHomotopyData_of_no_other_sourceFace_outcome
      hlinks
      hconn
      hSC
      hNoFour
      hNoMove23
      hNoDescent
      hNoHigh
      start
      hstartRealized
      hstartThree
      hstartObstruction

  obtain ⟨H⟩ := hH

  obtain ⟨N, hN, hD, hcells⟩ :=
    H.exists_finite_squareGrid_dyadic_refinement_vertexStar_control_probe m

  exact ⟨p, H, N, hN, hD, hcells⟩

end Poincare
