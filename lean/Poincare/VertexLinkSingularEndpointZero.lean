import Poincare.VertexLinkSingularSimplexEvaluation

open CategoryTheory
open scoped Simplicial

namespace Poincare

theorem vertexLinkRepresentedEdgeSingularOneSimplex_eval_zero
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v) :
    (((TopCat.toSSetObjEquiv
      (TopCat.of (↥(triangulationTopologicalVertexLink K v)))
      (.op ⦋1⦌))
      (vertexLinkRepresentedEdgeSingularOneSimplex K v e he)
      (TopCat.stdSimplexHomeomorphI.{0}.symm
        (TopCat.I.homeomorph.{0}.symm
          (⟨0, by norm_num⟩ : unitInterval))))).1 =
        triangulationTopologicalGeometricVertex e.lo := by
  rw [vertexLinkRepresentedEdgeSingularOneSimplex_eval]
  simp only [Homeomorph.apply_symm_apply]
  exact (vertexLinkRepresentedEdgePath_endpoints K v e he).1

end Poincare
