import Poincare.VertexLinkSingularEndpointOne
import Poincare.SingularFaceNaturality

open CategoryTheory
open scoped Simplicial

namespace Poincare

theorem vertexLinkRepresentedEdgeSingularOneSimplex_face_one_eval
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v) :
    (TopCat.toSSetObjEquiv
      (TopCat.of (↥(triangulationTopologicalVertexLink K v)))
      (.op ⦋0⦌))
      ((TopCat.toSSet.obj
        (TopCat.of (↥(triangulationTopologicalVertexLink K v)))).δ
          (1 : Fin 2)
          (vertexLinkRepresentedEdgeSingularOneSimplex K v e he))
      (default : stdSimplex ℝ (Fin 1)) =
    vertexLinkRepresentedEdgePath K v e he
      (TopCat.I.homeomorph.{0}
        (TopCat.stdSimplexHomeomorphI.{0}
          (stdSimplex.map (1 : Fin 2).succAbove
            (default : stdSimplex ℝ (Fin 1))))) := by
  rw [singularOneSimplex_face_naturality]
  rw [vertexLinkRepresentedEdgeSingularOneSimplex_eval]
  rfl

end Poincare
