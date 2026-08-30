import Poincare.GlobalMove32ReentryLeastBoundaryEscapeOutsideTargets
import Poincare.GlobalRepresentedEdgeIncidenceSplit

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
At the least left-boundary escape from the anchor five-vertex carrier, the
actual predecessor/escape edge is represented and has closed-core tetrahedron
incidence exactly three or at least four.  The same represented tetrahedron is
retained together with its exclusion from all three anchor target tetrahedra.
-/
theorem finite_squareGrid_least_boundary_escape_edge_incidenceSplit_probe
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
        label ⟨0, hD⟩ j ∈ rho.verts ∧
        ¬ SameTetVertices rho
            (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
        ¬ SameTetVertices rho
            (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
        ¬ SameTetVertices rho
            (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
        ((K.tets.filter
            (fun tau =>
              label ⟨0, hD⟩ k ∈ tau.verts ∧
              label ⟨0, hD⟩ j ∈ tau.verts)).length = 3 ∨
          4 ≤ (K.tets.filter
            (fun tau =>
              label ⟨0, hD⟩ k ∈ tau.verts ∧
              label ⟨0, hD⟩ j ∈ tau.verts)).length) := by
  classical
  dsimp only

  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, rho, hjPos, hkSucc, hkInside, hjOutside,
      hrho, hkRho, hjRho, hnot0, hnot1, hnot2⟩ :=
    finite_squareGrid_least_boundary_escape_outside_anchorTargets_probe
      hcore hlinks hNoFour p H N hN hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩
  let v : Nat := label i0 k
  let x : Nat := label i0 j

  have hkInside' :
      v ∈
        [(p.crossing.sites p.crossing.anchorIndex).a,
          (p.crossing.sites p.crossing.anchorIndex).b,
          (p.crossing.sites p.crossing.anchorIndex).c,
          (p.crossing.sites p.crossing.anchorIndex).d,
          (p.crossing.sites p.crossing.anchorIndex).e] := by
    simpa [v, i0] using hkInside

  have hjOutside' :
      x ∉
        [(p.crossing.sites p.crossing.anchorIndex).a,
          (p.crossing.sites p.crossing.anchorIndex).b,
          (p.crossing.sites p.crossing.anchorIndex).c,
          (p.crossing.sites p.crossing.anchorIndex).d,
          (p.crossing.sites p.crossing.anchorIndex).e] := by
    simpa [x, i0] using hjOutside

  have hvx : v ≠ x := by
    intro hvxEq
    apply hjOutside'
    rw [← hvxEq]
    exact hkInside'

  have hkRho' : v ∈ rho.verts := by
    simpa [v, i0] using hkRho

  have hjRho' : x ∈ rho.verts := by
    simpa [x, i0] using hjRho

  have hmem :
      rho ∈ K.tets.filter
        (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts) := by
    simp [hrho, hkRho', hjRho']

  have hpos :
      0 < (K.tets.filter
        (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length := by
    exact List.length_pos_iff_exists_mem.mpr ⟨rho, hmem⟩

  have hsplit :=
    hcore.edgeIncidence_eq_three_or_four_le_of_pos v x hvx hpos

  refine ⟨j, k, rho, hjPos, hkSucc, hkInside, hjOutside,
    hrho, hkRho, hjRho, hnot0, hnot1, hnot2, ?_⟩
  simpa [v, x, i0] using hsplit

end CarrierLoopNullHomotopyData
end Poincare
