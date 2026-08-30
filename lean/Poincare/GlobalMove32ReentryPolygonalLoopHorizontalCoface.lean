import Poincare.GlobalMove32ReentryPolygonalLoopFiniteCommonCofaceFillingFailClosed

namespace Poincare

/--
For any finite common-coface labelling of a square grid, horizontally adjacent
cell labels occur together in one represented tetrahedron.

This is the row-wise propagation primitive needed after anchoring the left
boundary to the recurrent Move32 geometry.  It asserts no Pachner exit, strict
descent, or contradiction.
-/
theorem CarrierLoopNullHomotopyData.horizontal_neighbor_labels_common_tet_of_common_coface
    {K : Triangulation}
    (D : Nat)
    (hD : 0 < D)
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
    (i j : Fin D)
    (hi : (i : Nat) + 1 < D) :
    ∃ tau ∈ K.tets,
      label i j ∈ tau.verts ∧
      label ⟨(i : Nat) + 1, hi⟩ j ∈ tau.verts := by
  let i1 : Fin D := ⟨(i : Nat) + 1, hi⟩

  have hstep (k : Fin D) :
      (CarrierLoopNullHomotopyData.squareGridParameter
          D hD k.castSucc : ℝ) ≤
        (CarrierLoopNullHomotopyData.squareGridParameter
          D hD k.succ : ℝ) := by
    have hDreal : 0 < (D : ℝ) := by
      exact_mod_cast hD
    change
      ((k : Nat) : ℝ) / (D : ℝ) ≤
        (((k : Nat) + 1 : Nat) : ℝ) / (D : ℝ)
    rw [div_le_div_iff_of_pos_right hDreal]
    norm_num

  have hxEq :
      CarrierLoopNullHomotopyData.squareGridParameter D hD i.succ =
        CarrierLoopNullHomotopyData.squareGridParameter D hD i1.castSucc := by
    apply Subtype.ext
    simp [CarrierLoopNullHomotopyData.squareGridParameter, i1]

  let z : unitInterval × unitInterval :=
    (CarrierLoopNullHomotopyData.squareGridParameter D hD i.succ,
      CarrierLoopNullHomotopyData.squareGridParameter D hD j.castSucc)

  have hz0 :
      z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i j := by
    simp only [CarrierLoopNullHomotopyData.squareGridCell]
    dsimp [z]
    exact ⟨hstep i, le_rfl, le_rfl, hstep j⟩

  have hz1 :
      z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i1 j := by
    simp only [CarrierLoopNullHomotopyData.squareGridCell]
    dsimp [z]
    have hxReal :
        (CarrierLoopNullHomotopyData.squareGridParameter
            D hD i1.castSucc : ℝ) =
          (CarrierLoopNullHomotopyData.squareGridParameter
            D hD i.succ : ℝ) := by
      exact congrArg (fun t : unitInterval => (t : ℝ)) hxEq.symm
    exact ⟨le_of_eq hxReal, hstep i1, le_rfl, hstep j⟩

  let S : Finset (Fin D × Fin D) := {(i, j), (i1, j)}

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
  · simpa using hlabels (i, j) (by simp [S])
  · simpa [i1] using hlabels (i1, j) (by simp [S])

end Poincare
