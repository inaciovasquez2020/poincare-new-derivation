import Poincare.GlobalMove32ReentryLeastBoundaryEscape

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
At the least left-boundary escape from the anchor carrier, the escaping label
and its immediate predecessor occur together in one represented tetrahedron.
The predecessor is still one of the five anchor vertices, while the escaping
label is outside all five.

This is only the first-exit common-coface certificate.  It does not classify
the represented tetrahedron as a Pachner move, descent, or reentry.
-/
theorem finite_squareGrid_least_boundary_escape_commonCoface_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (N : Nat) (hN : 0 < N) :
    let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
    let D := N * 2 ^ (m + 1)
    ∀ (hD : 0 < D)
      (label : Fin D → Fin D → Nat),
      (∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) →
      ∃ j k : Fin D, ∃ rho : Tet,
        0 < (j : Nat) ∧
        (k : Nat) + 1 = (j : Nat) ∧
        label ⟨0, hD⟩ k ∈
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] ∧
        label ⟨0, hD⟩ j ∉
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] ∧
        rho ∈ K.tets ∧
        label ⟨0, hD⟩ k ∈ rho.verts ∧
        label ⟨0, hD⟩ j ∈ rho.verts := by
  dsimp only

  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, hjPos, hjOutside, _hbefore, k, hkSucc, hkInside⟩ :=
    finite_squareGrid_least_boundary_label_escape_probe
      hcore hlinks hNoFour p H N hN hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩

  obtain ⟨z, hzk, hzj⟩ :=
    (squareGridCell_neighbor_overlap_probe D hD).2 i0 k j hkSucc

  obtain ⟨rho, hrho, hkRho, hjRho⟩ :=
    carrier_two_positive_coordinates_common_tet_probe
      (H.homotopy z)
      (hpositive i0 k z hzk)
      (hpositive i0 j z hzj)

  refine ⟨j, k, rho, hjPos, hkSucc, ?_, ?_, hrho, ?_, ?_⟩
  · simpa [i0] using hkInside
  · simpa [i0] using hjOutside
  · simpa [i0] using hkRho
  · simpa [i0] using hjRho

end CarrierLoopNullHomotopyData
end Poincare
