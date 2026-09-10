import Poincare.GlobalMove32ReentryPolygonalLoopFiniteCofaceFillingFailClosed

namespace Poincare

/--
Strengthen the finite coface-labelled filling from pairwise overlap to the
finite simplex condition actually needed by a discrete disk argument.

Any finite family of refined grid cells with one common parameter point has
all of its chosen labels in one represented tetrahedron.  The proof uses the
strictly positive label coordinate retained on each whole cell.  No Pachner
exit, strict descent, or contradiction is asserted here.
-/
theorem ClosedTriangulationCore.exists_polygonalLoop_dyadic_squareGrid_finite_common_coface_labeling_of_no_other_sourceFace_outcome
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
              ∀ S : Finset (Fin (N * 2 ^ m) × Fin (N * 2 ^ m)),
                (∃ z,
                  ∀ ij ∈ S,
                    z ∈ CarrierLoopNullHomotopyData.squareGridCell
                      (N * 2 ^ m) hD ij.1 ij.2) →
                ∃ tau ∈ K.tets,
                  ∀ ij ∈ S,
                    label ij.1 ij.2 ∈ tau.verts := by
  classical

  obtain ⟨p, H, N, hN, hD, label, hsupport, hpositive, _hpair⟩ :=
    hcore.exists_polygonalLoop_dyadic_squareGrid_coface_labeling_of_no_other_sourceFace_outcome
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
      m

  refine ⟨p, H, N, hN, hD, label, hsupport, hpositive, ?_⟩

  intro S hoverlap
  obtain ⟨z, hz⟩ := hoverlap

  have hspace :
      (H.homotopy z).1 ∈
        (triangulationTopologicalGeometricComplex K).space :=
    (H.homotopy z).2

  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion] at hspace
  simp only [Set.mem_iUnion] at hspace
  obtain ⟨tau, htau, hbody⟩ := hspace

  refine ⟨tau, htau, ?_⟩
  intro ij hij

  have hpos :
      0 < (H.homotopy z).1 (label ij.1 ij.2) :=
    hpositive ij.1 ij.2 z (hz ij hij)

  by_contra hnot
  have hz0 :=
    triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
      tau (label ij.1 ij.2) hnot hbody
  linarith

end Poincare
