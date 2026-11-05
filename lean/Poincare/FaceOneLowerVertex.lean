import Poincare.VertexLinkEdgeEndpoints
import Poincare.VertexLinkSingularFaceOneEvaluation
import Poincare.SingularFaceOneEndpointZero

open CategoryTheory
open scoped Simplicial

namespace Poincare

theorem vertexLinkRepresentedEdgeSingularOneSimplex_face_one_lowerVertex
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v) :
    ((TopCat.toSSetObjEquiv
      (TopCat.of (↥(triangulationTopologicalVertexLink K v)))
      (.op ⦋0⦌))
      ((TopCat.toSSet.obj
        (TopCat.of (↥(triangulationTopologicalVertexLink K v)))).δ
          (1 : Fin 2)
          (vertexLinkRepresentedEdgeSingularOneSimplex K v e he))
      (default : stdSimplex ℝ (Fin 1))).1 =
    triangulationTopologicalGeometricVertex e.lo := by
  rw [vertexLinkRepresentedEdgeSingularOneSimplex_face_one_eval]
  rw [singularFaceOne_endpoint_zero]
  exact (vertexLinkRepresentedEdgePath_endpoints K v e he).1

end Poincare
