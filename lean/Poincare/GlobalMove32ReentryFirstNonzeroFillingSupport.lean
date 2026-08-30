import Poincare.GlobalMove32ReentryFirstNonzeroTargetSupport
import Poincare.GlobalMove32ReentryDyadicGridVertices

namespace Poincare
namespace CarrierLoopNullHomotopyData

/-- At refinement depth one beyond the ordered-transition count, the first
positive left-boundary grid vertex is shared by the first two boundary cells.
Both cell labels are therefore vertices of the anchor transition's initial
target tetrahedron; in particular the upper label is one of `a,b,d,e`. -/
theorem finite_squareGrid_first_nonzero_anchor_initialTarget_labels_probe
    {K : Triangulation}
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
        label ⟨0, hD⟩ ⟨0, hD⟩ ∈
            (p.steps p.crossing.anchorIndex).initialTarget.verts ∧
        label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈
            (p.steps p.crossing.anchorIndex).initialTarget.verts ∧
        (label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
            (p.crossing.sites p.crossing.anchorIndex).a ∨
          label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
            (p.crossing.sites p.crossing.anchorIndex).b ∨
          label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
            (p.crossing.sites p.crossing.anchorIndex).d ∨
          label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
            (p.crossing.sites p.crossing.anchorIndex).e) := by
  classical
  dsimp only
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  have hm : 0 < m := by
    dsimp [m]
    have hgap := p.crossing.gap
    omega

  have hpowPos : 0 < 2 ^ m := by
    positivity
  have hpowTwo : 2 ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    omega
  have hNone : 1 ≤ N := by
    omega
  have hDlower : 2 ≤ D := by
    dsimp [D]
    have hmul := Nat.mul_le_mul hNone hpowTwo
    simpa using hmul
  have hDtwo : 1 < D := by
    omega

  obtain ⟨u, hu, htarget⟩ :=
    p.first_nonzero_initialTarget_supported_probe N hN

  have huD : (u : ℝ) = 1 / (D : ℝ) := by
    simpa [D, m] using hu

  let i0 : Fin D := ⟨0, hD⟩
  let j0 : Fin D := ⟨0, hD⟩
  let j1 : Fin D := ⟨1, hDtwo⟩
  let z : unitInterval × unitInterval :=
    squareGridCellSource D hD i0 j1

  have hz1 : z ∈ squareGridCell D hD i0 j1 := by
    exact squareGridCellSource_mem_probe D hD i0 j1

  have hz0 : z ∈ squareGridCell D hD i0 j0 := by
    have hbelow := squareGridCellSource_mem_probe D hD i0 j0
    have hj : j1.castSucc = j0.succ := by
      apply Fin.ext
      rfl
    dsimp [z]
    simp only [squareGridCell, squareGridCellSource] at hbelow ⊢
    rcases hbelow with ⟨_, hxup, _, hyup⟩
    rw [hj]
    exact ⟨le_rfl, hxup, hyup, le_rfl⟩

  have hzFirst : z.1 = (0 : unitInterval) := by
    dsimp [z, squareGridCellSource]
    simpa [i0] using squareGridParameter_zero_probe D hD

  have hzSecond : z.2 = u := by
    apply Subtype.ext
    dsimp [z, squareGridCellSource, squareGridParameter, j1]
    simpa [huD]

  have hzEq : z = ((0 : unitInterval), u) := by
    apply Prod.ext
    · exact hzFirst
    · exact hzSecond

  have hloop : H.homotopy z = p.polygonalLoop u := by
    rw [hzEq]
    exact H.loop_boundary u

  have hpositive0 :
      0 < (p.polygonalLoop u).1 (label i0 j0) := by
    have h := hpositive i0 j0 z hz0
    rw [hloop] at h
    exact h

  have hpositive1 :
      0 < (p.polygonalLoop u).1 (label i0 j1) := by
    have h := hpositive i0 j1 z hz1
    rw [hloop] at h
    exact h

  have hlabel0Target :
      label i0 j0 ∈
        (p.steps p.crossing.anchorIndex).initialTarget.verts := by
    by_contra hnot
    have hz :=
      triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
        (p.steps p.crossing.anchorIndex).initialTarget
        (label i0 j0) hnot htarget
    linarith

  have hlabel1Target :
      label i0 j1 ∈
        (p.steps p.crossing.anchorIndex).initialTarget.verts := by
    by_contra hnot
    have hz :=
      triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
        (p.steps p.crossing.anchorIndex).initialTarget
        (label i0 j1) hnot htarget
    linarith

  have hlabel1Target0 :
      label i0 j1 ∈
        (p.crossing.sites p.crossing.anchorIndex).targetTet₀.verts := by
    exact
      ((p.steps p.crossing.anchorIndex).initialTarget_same
        (label i0 j1)).1 hlabel1Target

  have hclass :
      label i0 j1 = (p.crossing.sites p.crossing.anchorIndex).a ∨
        label i0 j1 = (p.crossing.sites p.crossing.anchorIndex).b ∨
        label i0 j1 = (p.crossing.sites p.crossing.anchorIndex).d ∨
        label i0 j1 = (p.crossing.sites p.crossing.anchorIndex).e := by
    simpa [Move32Site.targetTet₀, Tet.verts] using hlabel1Target0

  refine ⟨hDtwo, ?_, ?_, ?_⟩
  · simpa [i0, j0] using hlabel0Target
  · simpa [i0, j1] using hlabel1Target
  · simpa [i0, j1] using hclass

end CarrierLoopNullHomotopyData
end Poincare
