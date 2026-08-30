import Poincare.GlobalMove32ReentryLeastBoundaryEscapeCoface

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
At the least left-boundary escape from the anchor five-vertex carrier, the
represented tetrahedron containing the predecessor/escape pair is not any of
the anchor Move32 target tetrahedra.  The reason is exact: the escaping label
belongs to that represented tetrahedron but to none of the five anchor
vertices, whereas every anchor target tetrahedron is supported on four of
those five vertices.
-/
theorem finite_squareGrid_least_boundary_escape_outside_anchorTargets_probe
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
            (p.crossing.sites p.crossing.anchorIndex).targetTet₂ := by
  classical
  dsimp only
  let s : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, rho, hjPos, hkSucc, hkInside, hjOutside,
      hrho, hkRho, hjRho⟩ :=
    finite_squareGrid_least_boundary_escape_commonCoface_probe
      hcore hlinks hNoFour p H N hN hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩

  have hjOutside' :
      label i0 j ∉ [s.a, s.b, s.c, s.d, s.e] := by
    simpa [i0, s] using hjOutside

  have hnot0 : ¬ SameTetVertices rho s.targetTet₀ := by
    intro hsame
    have hmem : label i0 j ∈ s.targetTet₀.verts := by
      exact (hsame (label i0 j)).1 (by simpa [i0] using hjRho)
    apply hjOutside'
    simp only [Move32Site.targetTet₀, Tet.verts, List.mem_cons,
      List.mem_singleton] at hmem ⊢
    aesop

  have hnot1 : ¬ SameTetVertices rho s.targetTet₁ := by
    intro hsame
    have hmem : label i0 j ∈ s.targetTet₁.verts := by
      exact (hsame (label i0 j)).1 (by simpa [i0] using hjRho)
    apply hjOutside'
    simp only [Move32Site.targetTet₁, Tet.verts, List.mem_cons,
      List.mem_singleton] at hmem ⊢
    aesop

  have hnot2 : ¬ SameTetVertices rho s.targetTet₂ := by
    intro hsame
    have hmem : label i0 j ∈ s.targetTet₂.verts := by
      exact (hsame (label i0 j)).1 (by simpa [i0] using hjRho)
    apply hjOutside'
    simp only [Move32Site.targetTet₂, Tet.verts, List.mem_cons,
      List.mem_singleton] at hmem ⊢
    aesop

  refine ⟨j, k, rho, hjPos, hkSucc, hkInside, hjOutside,
    hrho, hkRho, hjRho, ?_, ?_, ?_⟩
  · simpa [s] using hnot0
  · simpa [s] using hnot1
  · simpa [s] using hnot2

end CarrierLoopNullHomotopyData
end Poincare
