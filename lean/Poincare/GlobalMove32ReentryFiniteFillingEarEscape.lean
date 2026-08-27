import Poincare.GlobalMove32ReentryFiniteFillingEar

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Refine the first boundary ear/cancellation fork at the recurrent anchor.
The southwest filling label is positive at the anchor shared-edge midpoint,
so it is literally one of the two shared-edge endpoints `d` or `e`.

In the non-cancellation branch, the adjacent compatibility tetrahedron `rho`
either contains both shared-edge endpoints, in which case exact-three
saturation classifies it as one of the three recurrent anchor target
tetrahedra, or it contains exactly one endpoint and hence is not any anchor
target tetrahedron.  This is still not a legal Pachner-move statement.
-/
theorem finite_squareGrid_loopBoundary_anchor_firstEarEndpointFork_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (D : Nat)
    (hD : 0 < D)
    (hDtwo : 1 < D)
    (label : Fin D → Fin D → Nat)
    (hpositive :
      ∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) :
    ∃ tau : Tet,
      tau ∈ K.tets ∧
      label ⟨0, hD⟩ ⟨0, hD⟩ ∈ tau.verts ∧
      (label ⟨0, hD⟩ ⟨0, hD⟩ =
          (p.crossing.sites p.crossing.anchorIndex).d ∨
        label ⟨0, hD⟩ ⟨0, hD⟩ =
          (p.crossing.sites p.crossing.anchorIndex).e) ∧
      (((SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
            (p.crossing.sites p.crossing.anchorIndex).a ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).b ∈ tau.verts) ∨
          (SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
            (p.crossing.sites p.crossing.anchorIndex).a ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).c ∈ tau.verts) ∨
          (SameTetVertices tau
              (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
            (p.crossing.sites p.crossing.anchorIndex).b ∈ tau.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).c ∈ tau.verts)) ∧
        (label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ tau.verts ∨
          ∃ rho : Tet,
            rho ∈ K.tets ∧
            rho ≠ tau ∧
            label ⟨0, hD⟩ ⟨0, hD⟩ ∈ rho.verts ∧
            label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ rho.verts ∧
            ((((p.crossing.sites p.crossing.anchorIndex).d ∈ rho.verts ∧
                (p.crossing.sites p.crossing.anchorIndex).e ∈ rho.verts) ∧
                (SameTetVertices rho
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∨
                  SameTetVertices rho
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∨
                  SameTetVertices rho
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₂)) ∨
              ((((p.crossing.sites p.crossing.anchorIndex).d ∈ rho.verts ∧
                    (p.crossing.sites p.crossing.anchorIndex).e ∉ rho.verts) ∨
                  ((p.crossing.sites p.crossing.anchorIndex).e ∈ rho.verts ∧
                    (p.crossing.sites p.crossing.anchorIndex).d ∉ rho.verts)) ∧
                ¬ SameTetVertices rho
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
                ¬ SameTetVertices rho
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                ¬ SameTetVertices rho
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₂)))) := by
  let s : Move32Site :=
    p.crossing.sites p.crossing.anchorIndex
  let i0 : Fin D := ⟨0, hD⟩
  let j0 : Fin D := ⟨0, hD⟩
  let j1 : Fin D := ⟨1, hDtwo⟩

  have hsRealized : s.RealizedIn K := by
    exact p.realized p.crossing.anchorIndex

  have hanchorThree : s.SharedEdgeExactlyThree K := by
    have h :=
      p.ordered.sharedEdgeExactlyThree
        p.ordered.crossing.anchorIndex
        (by omega)
        (by
          have hg := p.ordered.crossing.gap
          omega)
    rw [p.ordered.traceAt_eq_site] at h
    rw [p.ordered_crossing] at h
    exact h

  obtain ⟨tau, htau, hlabel0Tau, hclass, hfork⟩ :=
    H.finite_squareGrid_loopBoundary_anchor_firstEarCancellationFork_probe
      hcore p D hD hDtwo label hpositive

  let z0 : unitInterval × unitInterval :=
    squareGridCellSource D hD i0 j0

  have hz0Cell : z0 ∈ squareGridCell D hD i0 j0 := by
    exact squareGridCellSource_mem_probe D hD i0 j0

  have hz0Second : z0.2 = (0 : unitInterval) := by
    dsimp [z0, squareGridCellSource]
    simpa [j0] using squareGridParameter_zero_probe D hD

  have hz0Source : H.homotopy z0 = p.basepoint := by
    have hzEq : z0 = (z0.1, (0 : unitInterval)) := by
      apply Prod.ext
      · rfl
      · exact hz0Second
    rw [hzEq]
    exact H.source_boundary z0.1

  have hlabel0Positive :
      0 < p.basepoint.1 (label i0 j0) := by
    have h := hpositive i0 j0 z0 hz0Cell
    rw [hz0Source] at h
    exact h

  have hlabel0Endpoint :
      label i0 j0 = s.d ∨ label i0 j0 = s.e := by
    rw [p.basepoint_eq] at hlabel0Positive
    change
      0 < triangulationTopologicalGeometricEdgeMidpoint
        s.d s.e (label i0 j0) at hlabel0Positive
    by_cases hd : label i0 j0 = s.d
    · exact Or.inl hd
    by_cases he : label i0 j0 = s.e
    · exact Or.inr he
    · have hsd : s.d ≠ label i0 j0 := by
        intro h
        exact hd h.symm
      have hse : s.e ≠ label i0 j0 := by
        intro h
        exact he h.symm
      exfalso
      simpa [triangulationTopologicalGeometricEdgeMidpoint_apply, hsd, hse]
        using hlabel0Positive

  refine ⟨tau, htau, hlabel0Tau, ?_, hclass, ?_⟩
  · simpa [i0, j0, s] using hlabel0Endpoint

  rcases hfork with hcancel | ⟨rho, hrho, hrhoNe, hlabel0Rho, hlabel1Rho⟩
  · exact Or.inl hcancel
  · right
    refine ⟨rho, hrho, hrhoNe, hlabel0Rho, hlabel1Rho, ?_⟩

    change label i0 j0 ∈ rho.verts at hlabel0Rho

    by_cases hdRho : s.d ∈ rho.verts
    · by_cases heRho : s.e ∈ rho.verts
      · left
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simpa [s] using hdRho
        · simpa [s] using heRho
        · have htargetRho :=
            hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
              s hsRealized hanchorThree hrho hdRho heRho
          simpa [s] using htargetRho
      · right
        have hnot0 : ¬ SameTetVertices rho s.targetTet₀ := by
          intro hsame
          apply heRho
          apply (hsame s.e).2
          simp [Move32Site.targetTet₀, Tet.verts]
        have hnot1 : ¬ SameTetVertices rho s.targetTet₁ := by
          intro hsame
          apply heRho
          apply (hsame s.e).2
          simp [Move32Site.targetTet₁, Tet.verts]
        have hnot2 : ¬ SameTetVertices rho s.targetTet₂ := by
          intro hsame
          apply heRho
          apply (hsame s.e).2
          simp [Move32Site.targetTet₂, Tet.verts]
        refine ⟨?_, ?_, ?_, ?_⟩
        · left
          exact ⟨by simpa [s] using hdRho, by simpa [s] using heRho⟩
        · simpa [s] using hnot0
        · simpa [s] using hnot1
        · simpa [s] using hnot2
    · by_cases heRho : s.e ∈ rho.verts
      · right
        have hnot0 : ¬ SameTetVertices rho s.targetTet₀ := by
          intro hsame
          apply hdRho
          apply (hsame s.d).2
          simp [Move32Site.targetTet₀, Tet.verts]
        have hnot1 : ¬ SameTetVertices rho s.targetTet₁ := by
          intro hsame
          apply hdRho
          apply (hsame s.d).2
          simp [Move32Site.targetTet₁, Tet.verts]
        have hnot2 : ¬ SameTetVertices rho s.targetTet₂ := by
          intro hsame
          apply hdRho
          apply (hsame s.d).2
          simp [Move32Site.targetTet₂, Tet.verts]
        refine ⟨?_, ?_, ?_, ?_⟩
        · right
          exact ⟨by simpa [s] using heRho, by simpa [s] using hdRho⟩
        · simpa [s] using hnot0
        · simpa [s] using hnot1
        · simpa [s] using hnot2
      · exfalso
        rcases hlabel0Endpoint with hd | he
        · apply hdRho
          rw [← hd]
          exact hlabel0Rho
        · apply heRho
          rw [← he]
          exact hlabel0Rho

end CarrierLoopNullHomotopyData
end Poincare
