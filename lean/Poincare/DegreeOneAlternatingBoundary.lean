import Poincare.VertexLinkEdgeEndpoints
import Mathlib.AlgebraicTopology.SingularHomology.Basic

namespace Poincare

open CategoryTheory

/--
The degree-one alternating differential is the
difference of the two face maps.

This is a general chain-complex identity, not a
vertex-link homology-comparison theorem.
-/
theorem degreeOneAlternatingBoundary_eq_faceDifference
    {C : Type*}
    [Category C]
    [Preadditive C]
    (X : SimplicialObject C) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).d 1 0 =
      X.δ (0 : Fin 2) - X.δ (1 : Fin 2) := by
  simp [
    AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD,
    Fin.sum_univ_two,
    sub_eq_add_neg
  ]

end Poincare
