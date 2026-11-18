import Poincare.GlobalMove32ReentryDyadicGridVertices

/-!
# Four-cell grid-node overlap

Four adjacent closed grid cells share a literal grid corner.
Their positive labels therefore lie in one represented tetrahedron.
No simply-connectedness or global Poincare hypothesis is assumed.
-/

namespace Poincare
namespace CarrierLoopNullHomotopyData

/-- The exact common point of four grid cells indexed by consecutive
horizontal and vertical positions is the southwest corner of their
northeast cell. -/
theorem squareGridCell_four_at_node_probe
    (N : Nat) (hN : 0 < N)
    (i i' j j' : Fin N)
    (hi : (i : Nat) + 1 = (i' : Nat))
    (hj : (j : Nat) + 1 = (j' : Nat)) :
    ∃ z : unitInterval × unitInterval,
      z ∈ squareGridCell N hN i j ∧
      z ∈ squareGridCell N hN i' j ∧
      z ∈ squareGridCell N hN i' j' ∧
      z ∈ squareGridCell N hN i j' := by
  let z := squareGridCellSource N hN i' j'
  have hsw := squareGridCellSource_mem_probe N hN i j
  have hne := squareGridCellSource_mem_probe N hN i' j'
  have hix : i'.castSucc = i.succ := by
    apply Fin.ext
    exact hi.symm
  have hjy : j'.castSucc = j.succ := by
    apply Fin.ext
    exact hj.symm
  simp only [squareGridCell, squareGridCellSource] at hsw hne
  rcases hsw with ⟨_, hxup, _, hyup⟩
  rcases hne with ⟨_, hxup', _, hyup'⟩
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  all_goals dsimp [z, squareGridCell, squareGridCellSource]
  all_goals rw [hix, hjy]
  · exact ⟨hxup, le_rfl, hyup, le_rfl⟩
  · exact ⟨le_rfl, hxup', hyup, le_rfl⟩
  · exact ⟨le_rfl, hxup', le_rfl, hyup'⟩
  · exact ⟨hxup, le_rfl, le_rfl, hyup'⟩

/-- Every four-cell junction in a positive-coordinate-labeled actual
carrier null-homotopy supplies one common represented tetrahedron. -/
theorem squareGrid_four_neighbor_labels_common_tet_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
      ∀ z ∈ squareGridCell N hN i j,
        0 < (H.homotopy z).1 (label i j))
    (i i' j j' : Fin N)
    (hi : (i : Nat) + 1 = (i' : Nat))
    (hj : (j : Nat) + 1 = (j' : Nat)) :
    ∃ tau : Tet, tau ∈ K.tets ∧
      label i j ∈ tau.verts ∧
      label i' j ∈ tau.verts ∧
      label i' j' ∈ tau.verts ∧
      label i j' ∈ tau.verts := by
  obtain ⟨z, hz00, hz10, hz11, hz01⟩ :=
    squareGridCell_four_at_node_probe N hN i i' j j' hi hj
  let s : Finset Nat :=
    {label i j, label i' j, label i' j', label i j'}
  have hs : ∀ v ∈ s, 0 < (H.homotopy z).1 v := by
    intro v hv
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h
    · rw [h]
      exact hpositive i j z hz00
    · rw [h]
      exact hpositive i' j z hz10
    · rw [h]
      exact hpositive i' j' z hz11
    · rw [h]
      exact hpositive i j' z hz01
  obtain ⟨tau, htau, hlabels⟩ :=
    carrier_finite_positive_coordinates_common_tet_probe
      (H.homotopy z) s hs
  refine ⟨tau, htau, ?_, ?_, ?_, ?_⟩
  all_goals apply hlabels
  all_goals simp [s]

#print axioms squareGridCell_four_at_node_probe
#print axioms squareGrid_four_neighbor_labels_common_tet_probe

end CarrierLoopNullHomotopyData
end Poincare
