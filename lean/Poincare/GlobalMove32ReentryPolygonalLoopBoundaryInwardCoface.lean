import Poincare.GlobalMove32ReentryPolygonalLoopFiniteCommonCofaceFillingFailClosed

namespace Poincare

/--
A finite common-coface labelling of a square grid already forces the first
boundary-to-interior combinatorial transition: for every left-boundary cell,
its label and the label of the immediately inward neighbouring cell occur
together in one represented tetrahedron.

This is purely a local consequence of the common-coface condition.  It does
not assert a Pachner exit, strict descent, or contradiction.
-/
theorem CarrierLoopNullHomotopyData.boundary_inward_labels_common_tet_of_common_coface
    {K : Triangulation}
    (D : Nat)
    (hD : 0 < D)
    (hDtwo : 1 < D)
    (label : Fin D → Fin D → Nat)
    (hcommon :
      ∀ S : Finset (Fin D × Fin D),
        (∃ z,
          ∀ ij ∈ S,
            z ∈ CarrierLoopNullHomotopyData.squareGridCell
              D hD ij.1 ij.2) →
        ∃ tau ∈ K.tets,
          ∀ ij ∈ S,
            label ij.1 ij.2 ∈ tau.verts)
    (j : Fin D) :
    ∃ tau ∈ K.tets,
      label ⟨0, hD⟩ j ∈ tau.verts ∧
      label ⟨1, hDtwo⟩ j ∈ tau.verts := by
  let i0 : Fin D := ⟨0, hD⟩
  let i1 : Fin D := ⟨1, hDtwo⟩

  have hstep (i : Fin D) :
      (CarrierLoopNullHomotopyData.squareGridParameter
          D hD i.castSucc : ℝ) ≤
        (CarrierLoopNullHomotopyData.squareGridParameter
          D hD i.succ : ℝ) := by
    have hDreal : 0 < (D : ℝ) := by
      exact_mod_cast hD
    change
      ((i : Nat) : ℝ) / (D : ℝ) ≤
        (((i : Nat) + 1 : Nat) : ℝ) / (D : ℝ)
    rw [div_le_div_iff_of_pos_right hDreal]
    norm_num

  have hxEq :
      CarrierLoopNullHomotopyData.squareGridParameter D hD i0.succ =
        CarrierLoopNullHomotopyData.squareGridParameter D hD i1.castSucc := by
    apply Subtype.ext
    simp [CarrierLoopNullHomotopyData.squareGridParameter, i0, i1]

  let z : unitInterval × unitInterval :=
    (CarrierLoopNullHomotopyData.squareGridParameter D hD i0.succ,
      CarrierLoopNullHomotopyData.squareGridParameter D hD j.castSucc)

  have hz0 :
      z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i0 j := by
    simp only [CarrierLoopNullHomotopyData.squareGridCell]
    dsimp [z]
    exact ⟨hstep i0, le_rfl, le_rfl, hstep j⟩

  have hz1 :
      z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i1 j := by
    simp only [CarrierLoopNullHomotopyData.squareGridCell]
    dsimp [z]
    have hxReal :
        (CarrierLoopNullHomotopyData.squareGridParameter
            D hD i1.castSucc : ℝ) =
          (CarrierLoopNullHomotopyData.squareGridParameter
            D hD i0.succ : ℝ) := by
      exact congrArg (fun t : unitInterval => (t : ℝ)) hxEq.symm
    exact ⟨le_of_eq hxReal, hstep i1, le_rfl, hstep j⟩

  let S : Finset (Fin D × Fin D) := {(i0, j), (i1, j)}

  have hoverlap :
      ∃ z,
        ∀ ij ∈ S,
          z ∈ CarrierLoopNullHomotopyData.squareGridCell
            D hD ij.1 ij.2 := by
    refine ⟨z, ?_⟩
    intro ij hij
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with hij | hij
    · subst ij
      exact hz0
    · subst ij
      exact hz1

  obtain ⟨tau, htau, hlabels⟩ := hcommon S hoverlap

  refine ⟨tau, htau, ?_, ?_⟩
  · simpa [i0] using hlabels (i0, j) (by simp [S])
  · simpa [i1] using hlabels (i1, j) (by simp [S])

end Poincare
