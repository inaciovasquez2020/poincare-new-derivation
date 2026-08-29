import Poincare.GlobalMove32ReentryPolygonalLoopFiniteBoundaryFillingFailClosed
import Poincare.GlobalMove32ReentryPolygonalLoopAnchorSupport

namespace Poincare

/--
For any positive-coordinate labelling of a square-grid filling of the ordered
recurrent polygonal loop, the left-boundary cell containing the source
parameter `t = 0` is labelled by one of the two endpoints of the anchor shared
edge.

This is the first exact attachment of the finite filling labels to the Move32
recurrence state.  It asserts no Pachner exit, strict descent, or contradiction.
-/
theorem WitnessedReentryPolygonalLoopCertificate.exists_boundary_source_cell_label_eq_anchor_endpoint
    {K : Triangulation}
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    {D : Nat}
    (hD : 0 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j z,
        z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i j →
          0 < (H.homotopy z).1 (label i j)) :
    ∃ j : Fin D,
      ((0 : unitInterval), (0 : unitInterval)) ∈
          CarrierLoopNullHomotopyData.squareGridCell
            D hD ⟨0, hD⟩ j ∧
      (label ⟨0, hD⟩ j =
          (p.crossing.sites p.crossing.anchorIndex).d ∨
       label ⟨0, hD⟩ j =
          (p.crossing.sites p.crossing.anchorIndex).e) := by
  obtain ⟨j, hcell, hboundary⟩ :=
    H.exists_squareGrid_loopBoundary_cell_probe
      D hD (0 : unitInterval)

  refine ⟨j, hcell, ?_⟩

  have hpos :
      0 <
        (H.homotopy ((0 : unitInterval), (0 : unitInterval))).1
          (label ⟨0, hD⟩ j) :=
    hpositive
      ⟨0, hD⟩
      j
      ((0 : unitInterval), (0 : unitInterval))
      hcell

  rw [hboundary] at hpos
  exact p.source_positive_coordinate_eq_anchor_endpoint hpos

end Poincare
