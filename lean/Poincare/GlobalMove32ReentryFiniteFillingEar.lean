import Poincare.GlobalMove32ReentryDyadicGridVertices

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Every label on the constant source boundary of a finite square-grid filling
shares a represented tetrahedron with one fixed represented vertex at the
basepoint.  This is the first boundary-cone reduction available from the
finite positive-coordinate filling; it does not yet assert a legal Pachner
move.
-/
theorem finite_squareGrid_sourceBoundary_commonApex_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (D : Nat)
    (hD : 0 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ apex : Nat,
      apex ∈ vertexSupport K ∧
      0 < x.1 apex ∧
      ∀ i : Fin D,
        ∃ tau : Tet,
          tau ∈ K.tets ∧
          label i ⟨0, hD⟩ ∈ tau.verts ∧
          apex ∈ tau.verts := by
  obtain ⟨apex, hapexSupport, hapexPositive⟩ :=
    carrier_exists_vertexSupport_coordinate_pos x

  refine ⟨apex, hapexSupport, hapexPositive, ?_⟩
  intro i

  let j0 : Fin D := ⟨0, hD⟩
  let z : unitInterval × unitInterval :=
    squareGridCellSource D hD i j0

  have hzCell : z ∈ squareGridCell D hD i j0 := by
    exact squareGridCellSource_mem_probe D hD i j0

  have hzSecond : z.2 = (0 : unitInterval) := by
    dsimp [z, squareGridCellSource]
    simpa [j0] using squareGridParameter_zero_probe D hD

  have hzSource : H.homotopy z = x := by
    have hzEq : z = (z.1, (0 : unitInterval)) := by
      apply Prod.ext
      · rfl
      · exact hzSecond
    rw [hzEq]
    exact H.source_boundary z.1

  have hlabelPositive : 0 < x.1 (label i j0) := by
    have h := hpositive i j0 z hzCell
    rw [hzSource] at h
    exact h

  exact carrier_two_positive_coordinates_common_tet_probe
    x hlabelPositive hapexPositive

/--
The finite filling is synchronized with the genuine loop boundary at the
recurrent anchor: a label on the left boundary at loop parameter zero occurs
in one represented tetrahedron together with the first endpoint of the
anchor shared edge.

This is deliberately weaker than a Pachner-ear statement.  It repairs the
boundary orientation first: `homotopy (0,t)` is the polygonal-loop boundary,
whereas `homotopy (s,0)` is constant.
-/
theorem finite_squareGrid_loopBoundary_anchor_endpoint_tet_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (D : Nat)
    (hD : 0 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ j : Fin D,
      ∃ tau : Tet,
        tau ∈ K.tets ∧
        label ⟨0, hD⟩ j ∈ tau.verts ∧
        (p.crossing.sites p.crossing.anchorIndex).d ∈ tau.verts := by
  let s : Move32Site :=
    p.crossing.sites p.crossing.anchorIndex

  have hsRealized : s.RealizedIn K := by
    exact p.realized p.crossing.anchorIndex

  have hde : s.d ≠ s.e :=
    (hcore.move32_sharedEdge_supported s hsRealized).2.2

  obtain ⟨j, hcell, hloop⟩ :=
    H.exists_squareGrid_loopBoundary_cell_probe
      D hD (0 : unitInterval)

  have hlabelPositive :
      0 < p.basepoint.1 (label ⟨0, hD⟩ j) := by
    have h :=
      hpositive ⟨0, hD⟩ j
        ((0 : unitInterval), (0 : unitInterval)) hcell
    rw [hloop] at h
    simpa using h

  have hdPositive : 0 < p.basepoint.1 s.d := by
    rw [p.basepoint_eq]
    change
      0 <
        triangulationTopologicalGeometricEdgeMidpoint
          s.d s.e s.d
    simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hde.symm]

  obtain ⟨tau, htau, hlabelTau, hdTau⟩ :=
    carrier_two_positive_coordinates_common_tet_probe
      p.basepoint hlabelPositive hdPositive

  exact ⟨j, tau, htau, hlabelTau, hdTau⟩

end CarrierLoopNullHomotopyData
end Poincare
