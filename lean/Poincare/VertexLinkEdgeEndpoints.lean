import Poincare.VertexLinkSingularEdgePath

namespace Poincare

/--
The continuous realization of a represented link edge
has the same endpoints as the combinatorial edge.

This establishes endpoint compatibility only.
It does not establish singular-chain boundary compatibility.
-/
theorem vertexLinkRepresentedEdgePath_endpoints
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v) :
    ((vertexLinkRepresentedEdgePath K v e he)
        ⟨0, by norm_num⟩).1 =
      triangulationTopologicalGeometricVertex e.lo
    ∧
    ((vertexLinkRepresentedEdgePath K v e he)
        ⟨1, by norm_num⟩).1 =
      triangulationTopologicalGeometricVertex e.hi := by
  constructor <;>
    simp [vertexLinkRepresentedEdgePath]

end Poincare
