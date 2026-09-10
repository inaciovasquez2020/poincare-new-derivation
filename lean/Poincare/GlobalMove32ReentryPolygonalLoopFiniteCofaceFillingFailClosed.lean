import Poincare.GlobalMove32ReentryPolygonalLoopNullHomotopyFailClosed
import Poincare.TriangulationTopologicalVertexStarNeighborhood

namespace Poincare

/--
Under the explicit exclusion of the other one-step source-face outcomes, the
ordered recurrent polygonal loop admits a finite dyadically refined relative
filling whose cells carry supported vertex labels with a stronger property
than mere closed-star membership: the chosen label coordinate stays strictly
positive on the whole cell.

Consequently, whenever two grid cells overlap, their two labels occur together
in some represented tetrahedron.  This is the first combinatorial coface
extraction from the finite filling.  It does not yet force a Pachner exit,
strict descent, or contradiction.
-/
theorem ClosedTriangulationCore.exists_polygonalLoop_dyadic_squareGrid_coface_labeling_of_no_other_sourceFace_outcome
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
              ∀ i j i' j',
                (∃ z,
                  z ∈ CarrierLoopNullHomotopyData.squareGridCell
                      (N * 2 ^ m) hD i j ∧
                  z ∈ CarrierLoopNullHomotopyData.squareGridCell
                      (N * 2 ^ m) hD i' j') →
                ∃ tau ∈ K.tets,
                  label i j ∈ tau.verts ∧
                  label i' j' ∈ tau.verts := by
  classical

  obtain ⟨p, hH⟩ :=
    hcore.exists_polygonalLoop_nullHomotopyData_of_no_other_sourceFace_outcome
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

  obtain ⟨H⟩ := hH

  obtain ⟨N, hN, hcommon⟩ :=
    H.exists_uniform_vertexSupport_coordinate_positive_scale_probe

  have hscale :=
    CarrierLoopNullHomotopyData.orderedTransition_refined_grid_scale_probe
      N m hN

  have hcellPositive :
      ∀ i j : Fin (N * 2 ^ m),
        ∃ v, v ∈ vertexSupport K ∧
          ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell
              (N * 2 ^ m) hscale.1 i j,
            0 < (H.homotopy z).1 v := by
    intro i j

    let a : unitInterval × unitInterval :=
      CarrierLoopNullHomotopyData.squareGridCellSource
        (N * 2 ^ m) hscale.1 i j

    obtain ⟨v, hvSupport, hvquarter⟩ :=
      carrier_exists_vertexSupport_coordinate_ge_quarter
        (H.homotopy a)

    refine ⟨v, hvSupport, ?_⟩
    intro z hz

    have hdRefined :
        dist a z ≤ 1 / ((N * 2 ^ m : Nat) : ℝ) := by
      exact
        CarrierLoopNullHomotopyData.squareGridCell_dist_source_le
          (N * 2 ^ m) hscale.1 i j hz

    have hdCommon :
        dist a z ≤ 1 / (N : ℝ) := by
      exact hdRefined.trans hscale.2

    exact hcommon v hvSupport a z hdCommon hvquarter

  choose label hlabel using hcellPositive

  refine ⟨p, H, N, hN, hscale.1, label, ?_, ?_, ?_⟩

  · intro i j
    exact (hlabel i j).1

  · intro i j z hz
    exact (hlabel i j).2 z hz

  · intro i j i' j' hoverlap
    obtain ⟨z, hz, hz'⟩ := hoverlap

    have hvpos :
        0 < (H.homotopy z).1 (label i j) :=
      (hlabel i j).2 z hz

    have hwpos :
        0 < (H.homotopy z).1 (label i' j') :=
      (hlabel i' j').2 z hz'

    have hspace :
        (H.homotopy z).1 ∈
          (triangulationTopologicalGeometricComplex K).space :=
      (H.homotopy z).2

    rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion] at hspace
    simp only [Set.mem_iUnion] at hspace
    obtain ⟨tau, htau, hbody⟩ := hspace

    have hvTau : label i j ∈ tau.verts := by
      by_contra hv
      have hz0 :=
        triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
          tau (label i j) hv hbody
      linarith

    have hwTau : label i' j' ∈ tau.verts := by
      by_contra hw
      have hz0 :=
        triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
          tau (label i' j') hw hbody
      linarith

    exact ⟨tau, htau, hvTau, hwTau⟩

end Poincare
