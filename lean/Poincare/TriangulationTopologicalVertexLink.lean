import Poincare.TriangulationTopologicalGeometricCarrier
import Poincare.VertexLink

open Set

namespace Poincare

/--
The represented vertex link realized in the same topology-bearing Pi-space as
the global triangulation.  Its filled faces are precisely the basis-vector
realizations of the represented `LinkTriangle`s at `v`.
-/
noncomputable def triangulationTopologicalVertexLink
    (K : Triangulation) (v : Nat) : Set (Nat → ℝ) :=
  ⋃ (σ : LinkTriangle) (_ : σ ∈ vertexLinkTriangles K v),
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑σ.verts.toFinset : Set Nat))

/-- Exact facewise membership in the global Pi-space vertex-link realization. -/
theorem mem_triangulationTopologicalVertexLink_iff
    (K : Triangulation) (v : Nat) (x : Nat → ℝ) :
    x ∈ triangulationTopologicalVertexLink K v ↔
      ∃ σ : LinkTriangle,
        σ ∈ vertexLinkTriangles K v ∧
        x ∈ convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑σ.verts.toFinset : Set Nat)) := by
  simp [triangulationTopologicalVertexLink]

/--
The Pi-space realization of every represented vertex link is genuinely a
subspace of the global geometric realization.
-/
theorem triangulationTopologicalVertexLink_subset_space
    (K : Triangulation) (v : Nat) :
    triangulationTopologicalVertexLink K v ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ :=
    (mem_triangulationTopologicalVertexLink_iff K v x).1 hx
  obtain ⟨τ, hτK, hτσ⟩ :=
    (mem_vertexLinkTriangles_iff K v σ).1 hσ
  apply (mem_triangulationTopologicalGeometricCarrier_iff K x).2
  refine ⟨σ.verts.toFinset, ?_, ⟨τ, hτK, ?_⟩, hxσ⟩
  · exact ⟨σ.v0, by simp [LinkTriangle.verts]⟩
  · intro y hy
    exact List.mem_toFinset.mpr
      (τ.linkTriangleAt?_verts_subset v σ hτσ y
        (List.mem_toFinset.mp hy))

end Poincare
