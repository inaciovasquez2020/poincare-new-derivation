import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.StdBasis
import Poincare.TriangulationPreAbstractComplex

namespace Poincare

noncomputable local instance : DecidableEq (Nat → ℝ) := Classical.decEq _

/-- The canonical basis-vector embedding into the topology-bearing Pi-space. -/
noncomputable def triangulationTopologicalGeometricVertex (i : Nat) : Nat → ℝ :=
  Pi.single i 1

/--
The geometric simplicial complex of a triangulation in the Pi-space `Nat → ℝ`,
whose canonical Pi topology will support the topological realization.
-/
noncomputable def triangulationTopologicalGeometricComplex (K : Triangulation) :
    Geometry.SimplicialComplex ℝ (Nat → ℝ) := by
  letI : DecidableEq (Nat → ℝ) := Classical.decEq _
  apply Geometry.SimplicialComplex.ofAffineIndependent (𝕜 := ℝ) (E := Nat → ℝ)
    ((triangulationPreAbstractComplex K).map
      triangulationTopologicalGeometricVertex)
  refine
    (Pi.linearIndependent_single_one Nat ℝ).affineIndependent.range.mono
      (fun x hx ↦ ?_)
  simp only [Set.mem_iUnion, Finset.mem_coe] at hx
  obtain ⟨_, ⟨_, _, rfl⟩, hx⟩ := hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, rfl⟩

theorem triangulationTopologicalGeometricComplex_toPreAbstractSimplicialComplex
    (K : Triangulation) :
    (triangulationTopologicalGeometricComplex K).toPreAbstractSimplicialComplex =
      (triangulationPreAbstractComplex K).map
        triangulationTopologicalGeometricVertex :=
  rfl

end Poincare
