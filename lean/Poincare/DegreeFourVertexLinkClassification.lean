import Poincare.Move41TopologyPreservingDescent
import Poincare.VertexLink

namespace Poincare

/-- A degree-four vertex in a closed triangulation core has the complete
tetrahedral-boundary link certificate. -/
theorem ClosedTriangulationCore.vertexLinkTetrahedralBoundaryCertificate_of_vertexDegree_eq_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hdegree : vertexDegree K v = 4) :
    VertexLinkTetrahedralBoundaryCertificate K hcore v := by
  apply vertexLinkTetrahedralBoundaryCertificate_of_vertexDefect_zero
  · simp [vertexDefect, targetDegree, hdegree]
  · intro x hrepresented
    exact hcore.vertexLinkStarDegreeTwo hrepresented

end Poincare
