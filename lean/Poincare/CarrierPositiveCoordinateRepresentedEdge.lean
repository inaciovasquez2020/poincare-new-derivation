import Poincare.CarrierPositiveCoordinateCover
import Poincare.VertexLink

namespace Poincare

/-- Two distinct labels with strictly positive coordinates at one carrier point
belong to one represented tetrahedron, hence represent an edge in the vertex
link sense used by the ambient cyclic-fan API. -/
theorem vertexLinkVertexRepresented_of_positive_coordinates
    {K : Triangulation}
    (p : triangulationTopologicalGeometricCarrier K)
    {v x : Nat}
    (hvx : v ≠ x)
    (hv : 0 < p.1 v)
    (hx : 0 < p.1 x) :
    VertexLinkVertexRepresented K v x := by
  have hp := p.2
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨tau, htau, hpbody⟩ := hp

  have hvtau : v ∈ tau.verts := by
    by_contra hvnot
    have hz :=
      triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
        tau v hvnot hpbody
    linarith

  have hxtau : x ∈ tau.verts := by
    by_contra hxnot
    have hz :=
      triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
        tau x hxnot hpbody
    linarith

  obtain ⟨sigma, hsigma, hlink⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
      K v tau htau hvtau

  refine ⟨sigma, hsigma, ?_⟩
  exact (tau.mem_linkTriangleAt?_iff v x sigma hlink hvx.symm).2 hxtau

end Poincare
