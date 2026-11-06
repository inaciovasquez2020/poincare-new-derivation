import Poincare.VertexLinkTriangleIntersection

open Set

namespace Poincare

/--
The convex hulls of any two finite sets of canonical
basis vertices intersect exactly in the convex hull
of their common vertices.
-/
theorem vertexLinkFiniteFace_convexHull_inter_eq_commonVertices
    (s t : Finset Nat) :
    convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑s : Set Nat)) ∩
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑t : Set Nat)) =
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑(s ∩ t) : Set Nat)) := by
  classical
  have hlin :
      LinearIndependent ℝ triangulationTopologicalGeometricVertex :=
    Pi.linearIndependent_single_one Nat ℝ
  have haff : AffineIndependent ℝ
      ((↑) :
        (↑(s.image triangulationTopologicalGeometricVertex ∪
          t.image triangulationTopologicalGeometricVertex) :
            Set (Nat → ℝ)) → Nat → ℝ) :=
    hlin.affineIndependent.range.mono (by
      intro z hz
      change z ∈
        s.image triangulationTopologicalGeometricVertex ∪
        t.image triangulationTopologicalGeometricVertex at hz
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
    (fun u : Finset (Nat → ℝ) => (↑u : Set (Nat → ℝ)))
    (Finset.image_inter _ _ hlin.injective).symm

end Poincare
