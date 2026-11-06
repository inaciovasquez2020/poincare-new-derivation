import Poincare.SingularFaceOneBasepoint

open CategoryTheory
open scoped Simplicial

namespace Poincare

theorem singularFaceOne_endpoint_zero :
    TopCat.I.homeomorph.{0}
      (TopCat.stdSimplexHomeomorphI.{0}
        (stdSimplex.map (1 : Fin 2).succAbove
          (default : stdSimplex ℝ (Fin 1)))) =
    (0 : unitInterval) := by
  rw [singularFaceOne_standardPoint]
  simp only [Homeomorph.apply_symm_apply]
  rfl

end Poincare
