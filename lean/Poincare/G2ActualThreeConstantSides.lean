import Poincare.G2PrimalEdgeCoordinateSupport

/-!
# Actual null-homotopy: exact labels of three constant sides

Each closed grid cell on a constant side meets that side at a
specific parameter-square point. Positive-coordinate labels must
therefore equal the canonical base vertex.

No separate assumptions about boundary labels are made.
-/

namespace Poincare

open CarrierLoopNullHomotopyData

/-- Each bottom-row closed cell contains its southwest corner at y=0. -/
theorem g2_bottom_cell_constant_point
    (N : Nat) (hN : 0 < N) (i : Fin N) :
    ∃ z : unitInterval × unitInterval,
      z ∈ squareGridCell N hN i ⟨0,hN⟩ ∧ z.2 = 0 := by
  refine ⟨squareGridCellSource N hN i ⟨0,hN⟩,
    squareGridCellSource_mem_probe N hN i ⟨0,hN⟩, ?_⟩
  change squareGridParameter N hN (⟨0,hN⟩ : Fin N).castSucc = 0
  exact squareGridParameter_zero_probe N hN

/-- Each top-row closed cell meets y=1 at its northwest corner. -/
theorem g2_top_cell_constant_point
    (N : Nat) (hN : 0 < N) (i : Fin N) :
    ∃ z : unitInterval × unitInterval,
      z ∈ squareGridCell N hN i ⟨N-1,by omega⟩ ∧ z.2 = 1 := by
  let j : Fin N := ⟨N-1,by omega⟩
  let z : unitInterval × unitInterval :=
    (squareGridParameter N hN i.castSucc, 1)
  have hsrc := squareGridCellSource_mem_probe N hN i j
  simp only [squareGridCell, squareGridCellSource] at hsrc
  rcases hsrc with ⟨hxl,hxu,_,_⟩
  refine ⟨z, ?_, rfl⟩
  change (squareGridParameter N hN i.castSucc : ℝ) ≤
      (squareGridParameter N hN i.castSucc : ℝ) ∧
    (squareGridParameter N hN i.castSucc : ℝ) ≤
      (squareGridParameter N hN i.succ : ℝ) ∧
    (squareGridParameter N hN j.castSucc : ℝ) ≤ 1 ∧
    (1 : ℝ) ≤ (squareGridParameter N hN j.succ : ℝ)
  refine ⟨le_rfl,hxu,?_,?_⟩
  · exact (squareGridParameter N hN j.castSucc).property.2
  · have hlast : j.succ = Fin.last N := by
      apply Fin.ext
      dsimp [j]
      omega
    rw [hlast, squareGridParameter_last_probe]
    exact le_rfl

/-- Each right-column closed cell meets x=1 at its southeast corner. -/
theorem g2_right_cell_constant_point
    (N : Nat) (hN : 0 < N) (j : Fin N) :
    ∃ z : unitInterval × unitInterval,
      z ∈ squareGridCell N hN ⟨N-1,by omega⟩ j ∧ z.1 = 1 := by
  let i : Fin N := ⟨N-1,by omega⟩
  let z : unitInterval × unitInterval :=
    (1, squareGridParameter N hN j.castSucc)
  have hsrc := squareGridCellSource_mem_probe N hN i j
  simp only [squareGridCell, squareGridCellSource] at hsrc
  rcases hsrc with ⟨_,_,hyl,hyu⟩
  refine ⟨z, ?_, rfl⟩
  change (squareGridParameter N hN i.castSucc : ℝ) ≤ 1 ∧
    (1 : ℝ) ≤ (squareGridParameter N hN i.succ : ℝ) ∧
    (squareGridParameter N hN j.castSucc : ℝ) ≤
      (squareGridParameter N hN j.castSucc : ℝ) ∧
    (squareGridParameter N hN j.castSucc : ℝ) ≤
      (squareGridParameter N hN j.succ : ℝ)
  refine ⟨?_,?_,le_rfl,hyu⟩
  · exact (squareGridParameter N hN i.castSucc).property.2
  · have hlast : i.succ = Fin.last N := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [hlast, squareGridParameter_last_probe]
    exact le_rfl

/-- The actual carrier null-homotopy forces all three constant-side
cell-label sequences to equal the original primal base vertex. -/
theorem g2_carrier_grid_three_constant_sides_labels
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
       ∀ z ∈ squareGridCell N hN i j,
         0 < (H.homotopy z).1 (label i j))
    (u : Nat) (hbase : x.1 = triangulationTopologicalGeometricVertex u) :
    (∀ i : Fin N, label i ⟨0,hN⟩ = u) ∧
    (∀ i : Fin N, label i ⟨N-1,by omega⟩ = u) ∧
    (∀ j : Fin N, label ⟨N-1,by omega⟩ j = u) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    obtain ⟨z,hcell,hboundary⟩ := g2_bottom_cell_constant_point N hN i
    exact carrier_grid_constant_boundary_cell_label_eq_base_vertex
      H N hN label hpositive u hbase i ⟨0,hN⟩ z hcell
      (Or.inr (Or.inl hboundary))
  · intro i
    obtain ⟨z,hcell,hboundary⟩ := g2_top_cell_constant_point N hN i
    exact carrier_grid_constant_boundary_cell_label_eq_base_vertex
      H N hN label hpositive u hbase i ⟨N-1,by omega⟩ z hcell
      (Or.inr (Or.inr hboundary))
  · intro j
    obtain ⟨z,hcell,hboundary⟩ := g2_right_cell_constant_point N hN j
    exact carrier_grid_constant_boundary_cell_label_eq_base_vertex
      H N hN label hpositive u hbase ⟨N-1,by omega⟩ j z hcell
      (Or.inl hboundary)

#print axioms g2_bottom_cell_constant_point
#print axioms g2_top_cell_constant_point
#print axioms g2_right_cell_constant_point
#print axioms g2_carrier_grid_three_constant_sides_labels

end Poincare
