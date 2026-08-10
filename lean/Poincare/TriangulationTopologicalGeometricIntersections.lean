import Poincare.TriangulationTopologicalGeometricDecomposition

open Set

namespace Poincare

noncomputable local instance : DecidableEq (Nat → ℝ) := Classical.decEq _

/--
Two represented filled tetrahedra in the canonical topology-bearing
realization intersect exactly in the convex hull of their common vertex
labels.
-/
theorem triangulationTopologicalTetrahedron_inter_eq_commonFace
    (K : Triangulation) (τ ρ : Tet)
    (hτ : τ ∈ K.tets) (hρ : ρ ∈ K.tets) :
    convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑τ.verts.toFinset : Set Nat)) ∩
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑ρ.verts.toFinset : Set Nat)) =
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑(τ.verts.toFinset ∩ ρ.verts.toFinset) : Set Nat)) := by
  let s : Finset (Nat → ℝ) :=
    τ.verts.toFinset.image triangulationTopologicalGeometricVertex
  let t : Finset (Nat → ℝ) :=
    ρ.verts.toFinset.image triangulationTopologicalGeometricVertex
  have hs :
      s ∈ (triangulationTopologicalGeometricComplex K).faces := by
    rw [triangulationTopologicalGeometricComplex_toPreAbstractSimplicialComplex]
    change s ∈ Set.image
      (fun F : Finset Nat => F.image triangulationTopologicalGeometricVertex)
      (triangulationPreAbstractComplex K).faces
    refine ⟨τ.verts.toFinset, ?_, rfl⟩
    exact ⟨⟨τ.v0, by simp [Tet.verts]⟩, τ, hτ, Finset.Subset.rfl⟩
  have ht :
      t ∈ (triangulationTopologicalGeometricComplex K).faces := by
    rw [triangulationTopologicalGeometricComplex_toPreAbstractSimplicialComplex]
    change t ∈ Set.image
      (fun F : Finset Nat => F.image triangulationTopologicalGeometricVertex)
      (triangulationPreAbstractComplex K).faces
    refine ⟨ρ.verts.toFinset, ?_, rfl⟩
    exact ⟨⟨ρ.v0, by simp [Tet.verts]⟩, ρ, hρ, Finset.Subset.rfl⟩
  have hinjective : Function.Injective triangulationTopologicalGeometricVertex :=
    (Pi.linearIndependent_single_one Nat ℝ).injective
  have hinter :=
    (triangulationTopologicalGeometricComplex K).convexHull_inter_convexHull hs ht
  rw [← Finset.coe_inter] at hinter
  have hst :
      s ∩ t =
        (τ.verts.toFinset ∩ ρ.verts.toFinset).image
          triangulationTopologicalGeometricVertex := by
    simpa only [s, t] using
      (Finset.image_inter τ.verts.toFinset ρ.verts.toFinset hinjective).symm
  rw [hst] at hinter
  simpa only [s, t, Finset.coe_image] using hinter

end Poincare
