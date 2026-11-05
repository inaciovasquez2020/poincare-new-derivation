import Poincare.VertexLinkSingularOneSimplex

open CategoryTheory
open scoped Simplicial

namespace Poincare

/--
Evaluation of the singular one-simplex constructed
from a represented vertex-link edge recovers the
original continuous path under the canonical
standard-simplex parametrization.
-/
theorem vertexLinkRepresentedEdgeSingularOneSimplex_eval
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v)
    (z : stdSimplex ℝ (Fin 2)) :
    (TopCat.toSSetObjEquiv
      (TopCat.of (↥(triangulationTopologicalVertexLink K v)))
      (.op ⦋1⦌))
      (vertexLinkRepresentedEdgeSingularOneSimplex K v e he) z =
    vertexLinkRepresentedEdgePath K v e he
      (TopCat.I.homeomorph.{0}
        (TopCat.stdSimplexHomeomorphI.{0} z)) := by
  unfold vertexLinkRepresentedEdgeSingularOneSimplex
  rw [Equiv.apply_symm_apply]
  rfl

end Poincare
