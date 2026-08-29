import Poincare.GlobalMove32ReentryFirstTransitionBoundaryLabelEscape
import Poincare.GlobalMove32ReentryFirstNonzeroFillingSupport
import Mathlib.Data.Nat.Find

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
The finite boundary escape supplied by the first-transition breakpoint has a
least occurrence.  Because the bottom boundary label is already supported in
the anchor transition's initial target tetrahedron, this least escape is
strictly positive and has an immediate predecessor still carried by the five
anchor vertices.

This is only the finite first-exit certificate.  It does not yet classify the
inside-to-outside transition as a Pachner move, descent, or reentry.
-/
theorem finite_squareGrid_least_boundary_label_escape_probe
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
      ∃ j : Fin D,
        0 < (j : Nat) ∧
        label ⟨0, hD⟩ j ∉
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] ∧
        (∀ k : Fin D,
          (k : Nat) < (j : Nat) →
          label ⟨0, hD⟩ k ∈
            [(p.crossing.sites p.crossing.anchorIndex).a,
              (p.crossing.sites p.crossing.anchorIndex).b,
              (p.crossing.sites p.crossing.anchorIndex).c,
              (p.crossing.sites p.crossing.anchorIndex).d,
              (p.crossing.sites p.crossing.anchorIndex).e]) ∧
        ∃ k : Fin D,
          (k : Nat) + 1 = (j : Nat) ∧
          label ⟨0, hD⟩ k ∈
            [(p.crossing.sites p.crossing.anchorIndex).a,
              (p.crossing.sites p.crossing.anchorIndex).b,
              (p.crossing.sites p.crossing.anchorIndex).c,
              (p.crossing.sites p.crossing.anchorIndex).d,
              (p.crossing.sites p.crossing.anchorIndex).e] := by
  dsimp only

  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩
  let j0 : Fin D := ⟨0, hD⟩

  obtain ⟨_hDtwo, hlabel0Target, _hlabel1Target, _hclass⟩ :=
    finite_squareGrid_first_nonzero_anchor_initialTarget_labels_probe
      p H N hN hD label hpositive

  have hlabel0Target' :
      label i0 j0 ∈
        (p.steps p.crossing.anchorIndex).initialTarget.verts := by
    simpa [i0, j0] using hlabel0Target

  have hlabel0Target0 :
      label i0 j0 ∈
        (p.crossing.sites p.crossing.anchorIndex).targetTet₀.verts := by
    exact
      ((p.steps p.crossing.anchorIndex).initialTarget_same
        (label i0 j0)).1 hlabel0Target'

  have hlabel0Anchor :
      label i0 j0 ∈
        [(p.crossing.sites p.crossing.anchorIndex).a,
          (p.crossing.sites p.crossing.anchorIndex).b,
          (p.crossing.sites p.crossing.anchorIndex).c,
          (p.crossing.sites p.crossing.anchorIndex).d,
          (p.crossing.sites p.crossing.anchorIndex).e] := by
    simp only [Move32Site.targetTet₀, Tet.verts, List.mem_cons,
      List.mem_singleton] at hlabel0Target0 ⊢
    aesop

  obtain ⟨jExit, _hjParam, hjExit⟩ :=
    finite_squareGrid_first_transition_boundary_label_outside_anchorCarrier_probe
      hcore hlinks hNoFour p H N hN hD label hpositive

  let P : Nat → Prop := fun n =>
    ∃ hn : n < D,
      label i0 ⟨n, hn⟩ ∉
        [(p.crossing.sites p.crossing.anchorIndex).a,
          (p.crossing.sites p.crossing.anchorIndex).b,
          (p.crossing.sites p.crossing.anchorIndex).c,
          (p.crossing.sites p.crossing.anchorIndex).d,
          (p.crossing.sites p.crossing.anchorIndex).e]

  have hP : ∃ n, P n := by
    refine ⟨(jExit : Nat), ?_⟩
    dsimp [P]
    refine ⟨jExit.isLt, ?_⟩
    simpa [i0] using hjExit

  let n : Nat := Nat.find hP

  have hnSpec : P n := by
    simpa [n] using Nat.find_spec hP

  dsimp [P] at hnSpec
  obtain ⟨hnD, hnOutside⟩ := hnSpec

  let j : Fin D := ⟨n, hnD⟩

  have hnOutside' :
      label i0 j ∉
        [(p.crossing.sites p.crossing.anchorIndex).a,
          (p.crossing.sites p.crossing.anchorIndex).b,
          (p.crossing.sites p.crossing.anchorIndex).c,
          (p.crossing.sites p.crossing.anchorIndex).d,
          (p.crossing.sites p.crossing.anchorIndex).e] := by
    simpa [j] using hnOutside

  have hnPos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hnZero
    have hjEq : j = j0 := by
      apply Fin.ext
      simpa [j, j0, hnZero]
    rw [hjEq] at hnOutside'
    exact hnOutside' hlabel0Anchor

  have hbefore :
      ∀ k : Fin D,
        (k : Nat) < n →
        label i0 k ∈
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] := by
    intro k hk
    by_contra hkOutside
    have hkP : P (k : Nat) := by
      dsimp [P]
      exact ⟨k.isLt, hkOutside⟩
    have hkFind : (k : Nat) < Nat.find hP := by
      simpa [n] using hk
    exact (Nat.find_min hP hkFind) hkP

  have hkPredD : n - 1 < D := by
    omega

  let kPred : Fin D := ⟨n - 1, hkPredD⟩

  have hkPredLt : (kPred : Nat) < n := by
    dsimp [kPred]
    omega

  have hkPredInside := hbefore kPred hkPredLt

  have hkPredSucc : (kPred : Nat) + 1 = n := by
    dsimp [kPred]
    omega

  refine ⟨j, ?_, hnOutside', ?_, ?_⟩
  · simpa [j] using hnPos
  · intro k hk
    have hk' : (k : Nat) < n := by
      simpa [j] using hk
    exact hbefore k hk'
  · refine ⟨kPred, ?_, hkPredInside⟩
    simpa [j] using hkPredSucc

end CarrierLoopNullHomotopyData
end Poincare
