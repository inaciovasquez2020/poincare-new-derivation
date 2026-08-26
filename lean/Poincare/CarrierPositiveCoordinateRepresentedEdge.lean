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
  obtain ⟨F, _hF, tau, htau, hFtau, w, _hw0, _hw1, hwp⟩ :=
    carrier_exists_finite_barycentric_support p

  have hvF : v ∈ F := by
    by_contra hvnot
    have hz := geometricVertex_weighted_sum_coordinate F w p.1 hwp v
    rw [if_neg hvnot] at hz
    linarith

  have hxF : x ∈ F := by
    by_contra hxnot
    have hz := geometricVertex_weighted_sum_coordinate F w p.1 hwp x
    rw [if_neg hxnot] at hz
    linarith

  have hvtau : v ∈ tau.verts :=
    List.mem_toFinset.mp (hFtau hvF)

  have hxtau : x ∈ tau.verts :=
    List.mem_toFinset.mp (hFtau hxF)

  obtain ⟨sigma, hsigma, hlink⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
      K v tau htau hvtau

  refine ⟨sigma, hsigma, ?_⟩
  exact (tau.mem_linkTriangleAt?_iff v x sigma hlink hvx.symm).2 hxtau

end Poincare
