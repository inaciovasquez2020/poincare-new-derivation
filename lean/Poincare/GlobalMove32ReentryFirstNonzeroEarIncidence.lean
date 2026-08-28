import Poincare.GlobalMove32ReentryFirstNonzeroFillingSupport
import Poincare.GlobalMove32ReentryFiniteFillingEar

namespace Poincare
namespace CarrierLoopNullHomotopyData

/-- On the first two left-boundary cells at the refined first-positive loop
point, either the upper label already lies in the southwest target tetrahedron,
or the ear-escape tetrahedron is accompanied by an exact source-vertex
incidence: a `targetTet₁` southwest tetrahedron forces the upper label to be
`b`, while a `targetTet₂` southwest tetrahedron forces it to be `a`.
A `targetTet₀` southwest tetrahedron cannot enter the non-cancellation branch. -/
theorem finite_squareGrid_first_nonzero_anchor_firstEar_sourceVertexFork_probe
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
                ((SameTetVertices tau
                      (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                    label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                      (p.crossing.sites p.crossing.anchorIndex).b) ∨
                  (SameTetVertices tau
                      (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
                    label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                      (p.crossing.sites p.crossing.anchorIndex).a)))) := by
  classical
  dsimp only
  let s : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨hDtwo, _, _, hlabel1Class⟩ :=
    H.finite_squareGrid_first_nonzero_anchor_initialTarget_labels_probe
      p N hN hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩
  let j0 : Fin D := ⟨0, hD⟩
  let j1 : Fin D := ⟨1, hDtwo⟩

  obtain ⟨tau, htau, hlabel0Tau, hclass, hfork⟩ :=
    H.finite_squareGrid_loopBoundary_anchor_firstEarCancellationFork_probe
      hcore p D hD hDtwo label hpositive

  refine ⟨hDtwo, tau, htau, hlabel0Tau, hclass, ?_⟩

  by_cases hcancel : label i0 j1 ∈ tau.verts
  · left
    simpa [i0, j1] using hcancel

  · right
    rcases hfork with hsame | ⟨rho, hrho, hrhoNe, hlabel0Rho, hlabel1Rho⟩
    · exact (hcancel (by simpa [i0, j1] using hsame)).elim
    · refine ⟨rho, hrho, hrhoNe, hlabel0Rho, hlabel1Rho, ?_⟩

      have hlabelClass :
          label i0 j1 = s.a ∨
            label i0 j1 = s.b ∨
            label i0 j1 = s.d ∨
            label i0 j1 = s.e := by
        simpa [i0, j1, s] using hlabel1Class

      change
        (SameTetVertices tau s.targetTet₀ ∧
            s.a ∈ tau.verts ∧ s.b ∈ tau.verts) ∨
          (SameTetVertices tau s.targetTet₁ ∧
            s.a ∈ tau.verts ∧ s.c ∈ tau.verts) ∨
          (SameTetVertices tau s.targetTet₂ ∧
            s.b ∈ tau.verts ∧ s.c ∈ tau.verts) at hclass

      rcases hclass with h0 | h1 | h2

      · exfalso
        have hdTau : s.d ∈ tau.verts := by
          apply (h0.1 s.d).2
          simp [Move32Site.targetTet₀, Tet.verts]
        have heTau : s.e ∈ tau.verts := by
          apply (h0.1 s.e).2
          simp [Move32Site.targetTet₀, Tet.verts]
        rcases hlabelClass with ha | hb | hd | he
        · apply hcancel
          rw [ha]
          exact h0.2.1
        · apply hcancel
          rw [hb]
          exact h0.2.2
        · apply hcancel
          rw [hd]
          exact hdTau
        · apply hcancel
          rw [he]
          exact heTau

      · left
        refine ⟨h1.1, ?_⟩
        have hdTau : s.d ∈ tau.verts := by
          apply (h1.1 s.d).2
          simp [Move32Site.targetTet₁, Tet.verts]
        have heTau : s.e ∈ tau.verts := by
          apply (h1.1 s.e).2
          simp [Move32Site.targetTet₁, Tet.verts]
        rcases hlabelClass with ha | hb | hd | he
        · exfalso
          apply hcancel
          rw [ha]
          exact h1.2.1
        · exact hb
        · exfalso
          apply hcancel
          rw [hd]
          exact hdTau
        · exfalso
          apply hcancel
          rw [he]
          exact heTau

      · right
        refine ⟨h2.1, ?_⟩
        have hdTau : s.d ∈ tau.verts := by
          apply (h2.1 s.d).2
          simp [Move32Site.targetTet₂, Tet.verts]
        have heTau : s.e ∈ tau.verts := by
          apply (h2.1 s.e).2
          simp [Move32Site.targetTet₂, Tet.verts]
        rcases hlabelClass with ha | hb | hd | he
        · exact ha
        · exfalso
          apply hcancel
          rw [hb]
          exact h2.2.1
        · exfalso
          apply hcancel
          rw [hd]
          exact hdTau
        · exfalso
          apply hcancel
          rw [he]
          exact heTau

end CarrierLoopNullHomotopyData
end Poincare
