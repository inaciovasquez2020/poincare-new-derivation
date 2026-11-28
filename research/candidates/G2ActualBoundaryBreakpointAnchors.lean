import Poincare.G2PrimalEdgeCoordinateSupport

/-!
# Genuine carrier boundary breakpoint anchors

Every parameter t where the original loop reaches a canonical primal
vertex anchors at least one actual cell on the loop-facing side of any
positive-coordinate grid. Moreover *every* boundary cell containing the
parameter t receives exactly that same vertex label.

This geometric statement avoids any hidden alignment or parameterization
assumption. It is not the final ordered boundary-word correspondence.
-/

namespace Poincare

open CarrierLoopNullHomotopyData

/-- Any actual loop breakpoint at a canonical primal vertex forces the
label of every containing left-column grid cell to that vertex. -/
theorem g2_actual_boundary_breakpoint_all_cell_labels
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
      ∀ z ∈ squareGridCell N hN i j,
        0 < (H.homotopy z).1 (label i j))
    (t : unitInterval) (u : Nat)
    (hvertex : (loop t).1 = triangulationTopologicalGeometricVertex u) :
    ∀ j : Fin N,
      ((0 : unitInterval), t) ∈ squareGridCell N hN ⟨0,hN⟩ j →
        label ⟨0,hN⟩ j = u := by
  intro j hcell
  exact carrier_grid_loopBoundary_vertex_forces_label
    H N hN label hpositive ⟨0,hN⟩ j t hcell u hvertex

/-- Every true primal vertex breakpoint has a finite left-boundary grid
cell carrying the same canonical vertex label, with no requirement that
the parameter t coincide with a grid line. -/
theorem g2_actual_boundary_breakpoint_has_label_anchor
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
      ∀ z ∈ squareGridCell N hN i j,
        0 < (H.homotopy z).1 (label i j))
    (t : unitInterval) (u : Nat)
    (hvertex : (loop t).1 = triangulationTopologicalGeometricVertex u) :
    ∃ j : Fin N,
      ((0 : unitInterval), t) ∈ squareGridCell N hN ⟨0,hN⟩ j ∧
      label ⟨0,hN⟩ j = u := by
  obtain ⟨j, hcell⟩ := exists_squareGrid_left_cell_probe N hN t
  exact ⟨j, hcell,
    g2_actual_boundary_breakpoint_all_cell_labels
      H N hN label hpositive t u hvertex j hcell⟩

#print axioms g2_actual_boundary_breakpoint_all_cell_labels
#print axioms g2_actual_boundary_breakpoint_has_label_anchor

end Poincare
