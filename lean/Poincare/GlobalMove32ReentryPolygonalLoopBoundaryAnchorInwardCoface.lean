import Poincare.GlobalMove32ReentryPolygonalLoopBoundaryAnchor
import Poincare.GlobalMove32ReentryPolygonalLoopBoundaryInwardCoface

namespace Poincare

/--
The source boundary attachment propagates one cell into the finite filling.

If the finite grid is positive-labelled and satisfies the common-coface
condition, then the immediately inward neighbour of the source boundary cell
shares a represented tetrahedron with one of the two endpoints of the anchor
Move32 shared edge.

This is only the first anchored boundary-to-interior coface.  It asserts no
Pachner exit, strict descent, or contradiction.
-/
theorem WitnessedReentryPolygonalLoopCertificate.exists_source_inward_label_common_tet_with_anchor_endpoint
    {K : Triangulation}
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    {D : Nat}
    (hD : 0 < D)
    (hDtwo : 1 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j z,
        z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i j →
          0 < (H.homotopy z).1 (label i j))
    (hcommon :
      ∀ S : Finset (Fin D × Fin D),
        (∃ z,
          ∀ ij ∈ S,
            z ∈ CarrierLoopNullHomotopyData.squareGridCell
              D hD ij.1 ij.2) →
        ∃ tau ∈ K.tets,
          ∀ ij ∈ S,
            label ij.1 ij.2 ∈ tau.verts) :
    ∃ j : Fin D, ∃ tau ∈ K.tets,
      ((p.crossing.sites p.crossing.anchorIndex).d ∈ tau.verts ∨
       (p.crossing.sites p.crossing.anchorIndex).e ∈ tau.verts) ∧
      label ⟨1, hDtwo⟩ j ∈ tau.verts := by
  obtain ⟨j, _, hanchor⟩ :=
    p.exists_boundary_source_cell_label_eq_anchor_endpoint
      H hD label hpositive

  obtain ⟨tau, htau, hboundaryTau, hinwardTau⟩ :=
    CarrierLoopNullHomotopyData.boundary_inward_labels_common_tet_of_common_coface
      D hD hDtwo label hcommon j

  refine ⟨j, tau, htau, ?_, hinwardTau⟩
  rcases hanchor with hanchor | hanchor
  · rw [hanchor] at hboundaryTau
    exact Or.inl hboundaryTau
  · rw [hanchor] at hboundaryTau
    exact Or.inr hboundaryTau

end Poincare
