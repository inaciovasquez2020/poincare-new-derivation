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

#print axioms geometric_primal_edge_coordinate_zero_off_endpoints
#print axioms geometric_primal_edge_positive_coordinate_is_endpoint

end Poincare
