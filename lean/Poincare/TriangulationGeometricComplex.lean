import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.Data.Real.Basic
import Poincare.TriangulationPreAbstractComplex

namespace Poincare

/-- The canonical basis-vector embedding of triangulation vertices. -/
noncomputable def triangulationGeometricVertex (i : Nat) : Nat →₀ ℝ :=
  Finsupp.single i 1

/-- The geometric simplicial complex associated to a triangulation. -/
noncomputable def triangulationGeometricComplex (K : Triangulation) :
    Geometry.SimplicialComplex ℝ (Nat →₀ ℝ) :=
  Geometry.SimplicialComplex.onFinsupp
    (𝕜 := ℝ)
    (triangulationPreAbstractComplex K)

theorem triangulationGeometricComplex_toPreAbstractSimplicialComplex (K : Triangulation) :
    (triangulationGeometricComplex K).toPreAbstractSimplicialComplex =
      (triangulationPreAbstractComplex K).map triangulationGeometricVertex :=
  rfl

end Poincare
