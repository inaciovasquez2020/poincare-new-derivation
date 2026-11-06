import Poincare.DegreeOneAlternatingBoundary
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

open CategoryTheory
open scoped Simplicial

namespace Poincare

/--
The face of a singular one-simplex is obtained by
precomposing with the corresponding standard-simplex
face inclusion.
-/
theorem singularOneSimplex_face_naturality
    (X : TopCat)
    (x : (TopCat.toSSet.obj X).obj (.op ⦋1⦌))
    (i : Fin 2)
    (z : stdSimplex ℝ (Fin 1)) :
    X.toSSetObjEquiv _
        ((TopCat.toSSet.obj X).δ i x) z =
      X.toSSetObjEquiv _ x
        (stdSimplex.map i.succAbove z) := by
  rfl

end Poincare
