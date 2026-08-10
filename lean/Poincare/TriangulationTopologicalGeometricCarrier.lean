import Poincare.TriangulationTopologicalGeometricComplex

open Set

namespace Poincare

noncomputable local instance : DecidableEq (Nat → ℝ) := Classical.decEq _

/--
The genuine topology-bearing realization of a triangulation: the subtype of
the space of its canonical Pi-space geometric simplicial complex.
-/
def triangulationTopologicalGeometricCarrier (K : Triangulation) :=
  ↥(triangulationTopologicalGeometricComplex K).space

/--
A point belongs to the topology-bearing realization exactly when it lies in
the convex hull of the basis-vector image of a nonempty face of a represented
tetrahedron.
-/
theorem mem_triangulationTopologicalGeometricCarrier_iff
    (K : Triangulation) (x : Nat → ℝ) :
    x ∈ (triangulationTopologicalGeometricComplex K).space ↔
      ∃ F : Finset Nat,
        F.Nonempty ∧
        (∃ τ : Tet, τ ∈ K.tets ∧ F ⊆ τ.verts.toFinset) ∧
        x ∈ convexHull ℝ
          (triangulationTopologicalGeometricVertex '' (↑F : Set Nat)) := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s, hs, hx⟩
    rw [triangulationTopologicalGeometricComplex_toPreAbstractSimplicialComplex] at hs
    change s ∈ Set.image
      (fun F : Finset Nat => F.image triangulationTopologicalGeometricVertex)
      (triangulationPreAbstractComplex K).faces at hs
    obtain ⟨F, hF, rfl⟩ := hs
    refine ⟨F, hF.1, hF.2, ?_⟩
    simpa only [Finset.coe_image] using hx
  · rintro ⟨F, hFnonempty, hFtet, hx⟩
    refine ⟨F.image triangulationTopologicalGeometricVertex, ?_, ?_⟩
    · rw [triangulationTopologicalGeometricComplex_toPreAbstractSimplicialComplex]
      change F.image triangulationTopologicalGeometricVertex ∈ Set.image
        (fun G : Finset Nat => G.image triangulationTopologicalGeometricVertex)
        (triangulationPreAbstractComplex K).faces
      exact ⟨F, ⟨hFnonempty, hFtet⟩, rfl⟩
    · simpa only [Finset.coe_image] using hx

end Poincare
