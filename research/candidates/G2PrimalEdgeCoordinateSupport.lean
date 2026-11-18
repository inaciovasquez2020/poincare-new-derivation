import Poincare.GlobalMove32ReentryDyadicGridVertices
import Poincare.CarrierPolygonalPath

/-!
# Coordinate support of primal edge segments

This proves the exact local endpoint restriction for straight canonical
primal-edge paths. It does not yet prove that a finite grid's perimeter
matches an arbitrary concatenation of such segments.
-/

namespace Poincare

/-- No coordinate outside the two canonical endpoint labels can be nonzero
anywhere on the affine segment. -/
theorem geometric_primal_edge_coordinate_zero_off_endpoints
    (u v j : Nat) (hju : j ≠ u) (hjv : j ≠ v) (t : ℝ) :
    (AffineMap.lineMap
      (triangulationTopologicalGeometricVertex u)
      (triangulationTopologicalGeometricVertex v) t) j = 0 := by
  simp [AffineMap.lineMap_apply,
    triangulationTopologicalGeometricVertex, hju, hjv]

/-- Strict positivity along an affine primal edge forces a label to be one
of its two endpoints, including the degenerate case u=v. -/
theorem geometric_primal_edge_positive_coordinate_is_endpoint
    (u v j : Nat) (t : ℝ)
    (hpos : 0 <
      (AffineMap.lineMap
        (triangulationTopologicalGeometricVertex u)
        (triangulationTopologicalGeometricVertex v) t) j) :
    j = u ∨ j = v := by
  by_contra h
  push_neg at h
  have hz :=
    geometric_primal_edge_coordinate_zero_off_endpoints
      u v j h.1 h.2 t
  rw [hz] at hpos
  exact (not_lt_of_ge le_rfl) hpos


/-- The actual homotopy boundary, evaluated at a point of a labeled closed
grid cell on the loop side, restricts its label to the two vertices of any
primal edge segment representing that boundary value. This is a *local*
boundary compatibility theorem: it does not assume the full loop has been
subdivided and aligned to the finite grid. -/
theorem carrier_grid_loopBoundary_label_is_edge_endpoint
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
       ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j,
         0 < (H.homotopy z).1 (label i j))
    (i j : Fin N) (t : unitInterval)
    (hcell :
      ((0 : unitInterval), t) ∈
        CarrierLoopNullHomotopyData.squareGridCell N hN i j)
    (u v : Nat) (s : ℝ)
    (hsegment :
      (loop t).1 = AffineMap.lineMap
        (triangulationTopologicalGeometricVertex u)
        (triangulationTopologicalGeometricVertex v) s) :
    label i j = u ∨ label i j = v := by
  have hp :=
    hpositive i j ((0 : unitInterval), t) hcell
  rw [H.loop_boundary t, hsegment] at hp
  exact geometric_primal_edge_positive_coordinate_is_endpoint
    u v (label i j) s hp



/-- A closed grid cell touching the loop at a canonical primal vertex
must carry precisely that vertex label, even when the breakpoint is
not aligned to a grid line. -/
theorem carrier_grid_loopBoundary_vertex_forces_label
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
       ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j,
         0 < (H.homotopy z).1 (label i j))
    (i j : Fin N) (t : unitInterval)
    (hcell :
      ((0 : unitInterval), t) ∈
        CarrierLoopNullHomotopyData.squareGridCell N hN i j)
    (u : Nat)
    (hvertex : (loop t).1 = triangulationTopologicalGeometricVertex u) :
    label i j = u := by
  have hp :=
    hpositive i j ((0 : unitInterval), t) hcell
  rw [H.loop_boundary t, hvertex] at hp
  by_contra hv
  have hz :
      triangulationTopologicalGeometricVertex u (label i j) = 0 := by
    simp [triangulationTopologicalGeometricVertex, hv, Ne.symm hv]
  rw [hz] at hp
  exact (not_lt_of_ge le_rfl) hp


/-- One positively labelled closed boundary cell cannot simultaneously
contain breakpoints representing two *different* primal vertices. This
rules out crossing an entire nondegenerate primal edge in one cell. -/
theorem carrier_grid_boundary_cell_breakpoints_same_vertex
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
       ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j,
         0 < (H.homotopy z).1 (label i j))
    (i j : Fin N) (s t : unitInterval)
    (hs :
      ((0 : unitInterval), s) ∈
        CarrierLoopNullHomotopyData.squareGridCell N hN i j)
    (ht :
      ((0 : unitInterval), t) ∈
        CarrierLoopNullHomotopyData.squareGridCell N hN i j)
    (u v : Nat)
    (hu : (loop s).1 = triangulationTopologicalGeometricVertex u)
    (hv : (loop t).1 = triangulationTopologicalGeometricVertex v) :
    u = v := by
  have hfirst :=
    carrier_grid_loopBoundary_vertex_forces_label
      H N hN label hpositive i j s hs u hu
  have hsecond :=
    carrier_grid_loopBoundary_vertex_forces_label
      H N hN label hpositive i j t ht v hv
  exact hfirst.symm.trans hsecond



/-- Every positively labelled grid cell containing a point whose carrier
coordinate is exactly the canonical vertex u must have label u.
This is independent of which parameter-square boundary is involved. -/
theorem carrier_grid_cell_vertex_forces_label
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
       ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j,
         0 < (H.homotopy z).1 (label i j))
    (i j : Fin N) (z : unitInterval × unitInterval)
    (hcell : z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j)
    (u : Nat)
    (hvertex : (H.homotopy z).1 =
      triangulationTopologicalGeometricVertex u) :
    label i j = u := by
  have hp := hpositive i j z hcell
  rw [hvertex] at hp
  by_contra hv
  have hz :
      triangulationTopologicalGeometricVertex u (label i j) = 0 := by
    simp [triangulationTopologicalGeometricVertex, hv, Ne.symm hv]
  rw [hz] at hp
  exact (not_lt_of_ge le_rfl) hp

/-- All labels on the three constant homotopy sides are the base vertex,
provided the basepoint is the canonical primal vertex u. -/
theorem carrier_grid_constant_boundary_cell_label_eq_base_vertex
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N)
    (label : Fin N → Fin N → Nat)
    (hpositive : ∀ i j : Fin N,
       ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j,
         0 < (H.homotopy z).1 (label i j))
    (u : Nat)
    (hbase : x.1 = triangulationTopologicalGeometricVertex u)
    (i j : Fin N) (z : unitInterval × unitInterval)
    (hcell : z ∈ CarrierLoopNullHomotopyData.squareGridCell N hN i j)
    (hconstant : z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1) :
    label i j = u := by
  have hpoint : H.homotopy z = x := by
    rcases hconstant with hright | hbottom | htop
    · have hz : z = ((1 : unitInterval), z.2) := by
        exact Prod.ext hright rfl
      rw [hz]
      exact H.constant_boundary z.2
    · have hz : z = (z.1, (0 : unitInterval)) := by
        exact Prod.ext rfl hbottom
      rw [hz]
      exact H.source_boundary z.1
    · have hz : z = (z.1, (1 : unitInterval)) := by
        exact Prod.ext rfl htop
      rw [hz]
      exact H.target_boundary z.1
  exact carrier_grid_cell_vertex_forces_label
    H N hN label hpositive i j z hcell u
    (by rw [hpoint]; exact hbase)


#print axioms geometric_primal_edge_coordinate_zero_off_endpoints
#print axioms geometric_primal_edge_positive_coordinate_is_endpoint
#print axioms carrier_grid_loopBoundary_label_is_edge_endpoint
#print axioms carrier_grid_loopBoundary_vertex_forces_label
#print axioms carrier_grid_boundary_cell_breakpoints_same_vertex
#print axioms carrier_grid_cell_vertex_forces_label
#print axioms carrier_grid_constant_boundary_cell_label_eq_base_vertex

end Poincare
