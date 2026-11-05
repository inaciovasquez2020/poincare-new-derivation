import Poincare.TriangulationTopologicalManifoldVertexLinkStarConnectedness

open Set

namespace Poincare

theorem vertexLinkTriangle_convexHull_inter_eq_commonVertices
    (a b : LinkTriangle) :
    convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑a.verts.toFinset : Set Nat)) ∩
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑b.verts.toFinset : Set Nat)) =
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑(a.verts.toFinset ∩ b.verts.toFinset) : Set Nat)) := by
  classical
  have hlin :
      LinearIndependent ℝ triangulationTopologicalGeometricVertex :=
    Pi.linearIndependent_single_one Nat ℝ
  have haff : AffineIndependent ℝ
      ((↑) :
        (↑(a.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
          b.verts.toFinset.image triangulationTopologicalGeometricVertex) :
            Set (Nat → ℝ)) → Nat → ℝ) :=
    hlin.affineIndependent.range.mono (by
      intro z hz
      change z ∈
        a.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
        b.verts.toFinset.image triangulationTopologicalGeometricVertex at hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
        exact Set.mem_range_self _
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
        exact Set.mem_range_self _)
  rw [← Finset.coe_image, ← Finset.coe_image, ← Finset.coe_image]
  rw [← haff.convexHull_inter']
  congr 2
  rw [← Finset.coe_inter]
  exact congrArg
    (fun s : Finset (Nat → ℝ) => (↑s : Set (Nat → ℝ)))
    (Finset.image_inter _ _ hlin.injective).symm

end Poincare
