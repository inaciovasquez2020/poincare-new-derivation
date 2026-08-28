import Poincare.GlobalMove32ReentryPolygonalLoopFiniteCommonCofaceFillingFailClosed

namespace Poincare

/--
Carry the finite common-coface filling to the actual loop boundary.

The left side of the null-homotopy square is exactly the ordered recurrent
polygonal loop.  Every loop parameter is therefore contained in a labelled
left-boundary grid cell, and that cell label has strictly positive coordinate
at the corresponding point of the polygonal loop.

This is a boundary-discretization theorem only.  It does not yet assert a
Pachner exit, strict descent, or contradiction.
-/
theorem ClosedTriangulationCore.exists_polygonalLoop_dyadic_squareGrid_boundary_labeling_of_no_other_sourceFace_outcome
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
            ∃ label : Fin (N * 2 ^ m) → Fin (N * 2 ^ m) → Nat,
              (∀ i j, label i j ∈ vertexSupport K) ∧
              (∀ i j z,
                z ∈ CarrierLoopNullHomotopyData.squareGridCell
                    (N * 2 ^ m) hD i j →
                  0 < (H.homotopy z).1 (label i j)) ∧
              (∀ S : Finset (Fin (N * 2 ^ m) × Fin (N * 2 ^ m)),
                (∃ z,
                  ∀ ij ∈ S,
                    z ∈ CarrierLoopNullHomotopyData.squareGridCell
                      (N * 2 ^ m) hD ij.1 ij.2) →
                ∃ tau ∈ K.tets,
                  ∀ ij ∈ S,
                    label ij.1 ij.2 ∈ tau.verts) ∧
              ∀ t : unitInterval,
                ∃ j : Fin (N * 2 ^ m),
                  ((0 : unitInterval), t) ∈
                      CarrierLoopNullHomotopyData.squareGridCell
                        (N * 2 ^ m) hD ⟨0, hD⟩ j ∧
                  H.homotopy ((0 : unitInterval), t) =
                    p.polygonalLoop t ∧
                  0 < (p.polygonalLoop t).1
                    (label ⟨0, hD⟩ j) := by
  obtain ⟨p, H, N, hN, hD, label, hsupport, hpositive, hcommon⟩ :=
    hcore.exists_polygonalLoop_dyadic_squareGrid_finite_common_coface_labeling_of_no_other_sourceFace_outcome
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
      m

  refine ⟨p, H, N, hN, hD, label, hsupport, hpositive, hcommon, ?_⟩
  intro t

  obtain ⟨j, hcell, hboundary⟩ :=
    H.exists_squareGrid_loopBoundary_cell_probe
      (N * 2 ^ m) hD t

  refine ⟨j, hcell, hboundary, ?_⟩

  have hpos :
      0 < (H.homotopy ((0 : unitInterval), t)).1
        (label ⟨0, hD⟩ j) :=
    hpositive ⟨0, hD⟩ j ((0 : unitInterval), t) hcell

  rw [hboundary] at hpos
  exact hpos

end Poincare
