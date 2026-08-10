import Poincare.TriangulationTopologicalGeometricCarrier

open Set

namespace Poincare

noncomputable local instance : DecidableEq (Nat → ℝ) := Classical.decEq _

/--
The topology-bearing realization is exactly the union of the filled
tetrahedra represented by `K.tets`.
-/
theorem triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion
    (K : Triangulation) :
    (triangulationTopologicalGeometricComplex K).space =
      ⋃ (τ : Tet) (_ : τ ∈ K.tets),
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑τ.verts.toFinset : Set Nat)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨F, hFnonempty, ⟨τ, hτK, hFτ⟩, hxF⟩ :=
      (mem_triangulationTopologicalGeometricCarrier_iff K x).1 hx
    simp only [mem_iUnion]
    refine ⟨τ, ⟨hτK, ?_⟩⟩
    apply convexHull_mono (Set.image_mono ?_) hxF
    intro i hi
    exact hFτ hi
  · simp only [mem_iUnion]
    rintro ⟨τ, hτK, hx⟩
    apply (mem_triangulationTopologicalGeometricCarrier_iff K x).2
    refine ⟨τ.verts.toFinset, ?_, ⟨τ, hτK, Finset.Subset.rfl⟩, hx⟩
    exact ⟨τ.v0, by simp [Tet.verts]⟩

end Poincare
