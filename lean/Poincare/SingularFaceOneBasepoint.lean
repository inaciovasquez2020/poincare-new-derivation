import Poincare.VertexLinkSingularFaceOneEvaluation

open CategoryTheory
open scoped Simplicial

namespace Poincare

theorem singularFaceOne_standardPoint :
    stdSimplex.map (1 : Fin 2).succAbove
      (default : stdSimplex ℝ (Fin 1)) =
    TopCat.stdSimplexHomeomorphI.{0}.symm
      (TopCat.I.homeomorph.{0}.symm
        (⟨0, by norm_num⟩ : unitInterval)) := by
  have hdefault :
      (default : stdSimplex ℝ (Fin 1)) =
        stdSimplex.vertex (0 : Fin 1) :=
    Subsingleton.elim _ _
  rw [hdefault]
  simp [
    stdSimplex.map_vertex,
    TopCat.stdSimplexHomeomorphI,
    TopCat.I.homeomorph
  ]
  apply stdSimplexHomeomorphUnitInterval.injective
  rw [stdSimplexHomeomorphUnitInterval.apply_symm_apply]
  exact stdSimplexHomeomorphUnitInterval_zero

end Poincare
