import Poincare.GlobalMove32ReentryFirstNonzeroEarIncidence
import Poincare.GlobalMove32ReentryFirstNonzeroCrossEdgeIncidence
import Poincare.GlobalMove32ReentryFirstNonzeroEarTargetTransition

namespace Poincare
namespace CarrierLoopNullHomotopyData

/-- Exhaust the first refined boundary-ear fork without asserting a source face
or a legal Pachner move.  Cancellation remains explicit.  Every genuine
escape is either two-sided, in which case the forced source vertex excludes
the matching target type, or one-sided, in which case one of the four anchor
cross edges is represented and has tetrahedron incidence exactly three or at
least four. -/
theorem finite_squareGrid_first_nonzero_anchor_firstEar_exhaustiveFork_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
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
      ∃ hDtwo : 1 < D,
        ∃ tau : Tet,
          tau ∈ K.tets ∧
          label ⟨0, hD⟩ ⟨0, hD⟩ ∈ tau.verts ∧
          (label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ tau.verts ∨
            ∃ rho : Tet,
              rho ∈ K.tets ∧
              rho ≠ tau ∧
              label ⟨0, hD⟩ ⟨0, hD⟩ ∈ rho.verts ∧
              label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ rho.verts ∧
              (((SameTetVertices tau
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                  label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                    (p.crossing.sites p.crossing.anchorIndex).b) ∨
                (SameTetVertices tau
                    (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
                  label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                    (p.crossing.sites p.crossing.anchorIndex).a)) ∧
                (((((p.crossing.sites p.crossing.anchorIndex).d ∈ rho.verts ∧
                        (p.crossing.sites p.crossing.anchorIndex).e ∈ rho.verts)) ∧
                    ((SameTetVertices tau
                          (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                        label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                          (p.crossing.sites p.crossing.anchorIndex).b ∧
                        (SameTetVertices rho
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∨
                          SameTetVertices rho
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₂)) ∨
                      (SameTetVertices tau
                          (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
                        label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                          (p.crossing.sites p.crossing.anchorIndex).a ∧
                        (SameTetVertices rho
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∨
                          SameTetVertices rho
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₁)))) ∨
                  (((((p.crossing.sites p.crossing.anchorIndex).d ∈ rho.verts ∧
                          (p.crossing.sites p.crossing.anchorIndex).e ∉ rho.verts) ∨
                        ((p.crossing.sites p.crossing.anchorIndex).e ∈ rho.verts ∧
                          (p.crossing.sites p.crossing.anchorIndex).d ∉ rho.verts)) ∧
                      ¬ SameTetVertices rho
                          (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
                      ¬ SameTetVertices rho
                          (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                      ¬ SameTetVertices rho
                          (p.crossing.sites p.crossing.anchorIndex).targetTet₂) ∧
                    ∃ v x : Nat,
                      ((v = (p.crossing.sites p.crossing.anchorIndex).b ∧
                          x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
                        (v = (p.crossing.sites p.crossing.anchorIndex).b ∧
                          x = (p.crossing.sites p.crossing.anchorIndex).e) ∨
                        (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
                          x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
                        (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
                          x = (p.crossing.sites p.crossing.anchorIndex).e)) ∧
                      v ∈ rho.verts ∧
                      x ∈ rho.verts ∧
                      ((K.tets.filter
                          (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length = 3 ∨
                        4 ≤ (K.tets.filter
                          (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length))))) := by
  classical
  dsimp only
  let s : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨hDtwo, tau, htau, hlabel0Tau, hfork⟩ :=
    H.finite_squareGrid_first_nonzero_anchor_firstEar_sourceEndpointEscape_probe
      hcore p N hN hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩
  let j0 : Fin D := ⟨0, hD⟩
  let j1 : Fin D := ⟨1, hDtwo⟩
  let s : Move32Site := p.crossing.sites p.crossing.anchorIndex

  refine ⟨hDtwo, tau, htau, hlabel0Tau, ?_⟩
  rcases hfork with hcancel |
      ⟨rho, hrho, hrhoNe, hlabel0Rho, hlabel1Rho, hsource, hside⟩
  · exact Or.inl hcancel
  · right
    refine ⟨rho, hrho, hrhoNe, hlabel0Rho, hlabel1Rho, hsource, ?_⟩

    have hsource' :
        (SameTetVertices tau s.targetTet₁ ∧ label i0 j1 = s.b) ∨
          (SameTetVertices tau s.targetTet₂ ∧ label i0 j1 = s.a) := by
      simpa [s, i0, j1] using hsource

    have hside' :
        ((s.d ∈ rho.verts ∧ s.e ∈ rho.verts) ∧
          (SameTetVertices rho s.targetTet₀ ∨
            SameTetVertices rho s.targetTet₁ ∨
            SameTetVertices rho s.targetTet₂)) ∨
        (((s.d ∈ rho.verts ∧ s.e ∉ rho.verts) ∨
            (s.e ∈ rho.verts ∧ s.d ∉ rho.verts)) ∧
          ¬ SameTetVertices rho s.targetTet₀ ∧
          ¬ SameTetVertices rho s.targetTet₁ ∧
          ¬ SameTetVertices rho s.targetTet₂) := by
      simpa [s] using hside

    have hsRealized : s.RealizedIn K := by
      simpa [s] using p.realized p.crossing.anchorIndex

    rcases hside' with htwo | hone
    · left
      refine ⟨htwo.1, ?_⟩
      exact hcore.move32_firstEar_target_transition_probe
        s hsRealized tau rho (label i0 j1) hsource' hlabel1Rho htwo.2

    · right
      have hsourceVertex : label i0 j1 = s.b ∨ label i0 j1 = s.a := by
        rcases hsource' with h1 | h2
        · exact Or.inl h1.2
        · exact Or.inr h2.2
      obtain ⟨v, x, hcross, hv, hx, hinc⟩ :=
        hcore.exists_crossEdge_incidenceSplit_of_move32_oneSided_sourceEndpoint_escape
          s hsRealized hrho hlabel1Rho hsourceVertex hone.1
      refine ⟨?_, v, x, ?_, hv, hx, hinc⟩
      · exact ⟨hone.1, hone.2.1, hone.2.2.1, hone.2.2.2⟩
      · simpa [s] using hcross

end CarrierLoopNullHomotopyData
end Poincare
