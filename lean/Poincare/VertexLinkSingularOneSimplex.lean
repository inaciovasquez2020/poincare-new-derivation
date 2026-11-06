import Poincare.SingularFaceNaturality
import Poincare.VertexLinkEdgeEndpoints
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

open CategoryTheory
open scoped Simplicial

namespace Poincare

/--
Construct a singular one-simplex from an existing
represented vertex-link edge path.

This does not establish boundary compatibility
or a homology comparison.
-/
noncomputable def vertexLinkRepresentedEdgeSingularOneSimplex
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v) :
    (TopCat.toSSet.obj
      (TopCat.of (↥(triangulationTopologicalVertexLink K v)))).obj
        (.op ⦋1⦌) :=
  (TopCat.toSSetObjEquiv
    (TopCat.of (↥(triangulationTopologicalVertexLink K v)))
    (.op ⦋1⦌)).symm
    ⟨fun z =>
      vertexLinkRepresentedEdgePath K v e he
        (TopCat.I.homeomorph.{0}
          (TopCat.stdSimplexHomeomorphI.{0} z)),
      (vertexLinkRepresentedEdgePath K v e he).continuous.comp
        (TopCat.I.homeomorph.{0}.continuous.comp
          TopCat.stdSimplexHomeomorphI.{0}.continuous)⟩

end Poincare
