import Poincare.VertexLinkRepresentedEdgeRealization
import Mathlib.Tactic

open Set

namespace Poincare

/--
A represented combinatorial vertex-link edge determines
a continuous path within the actual topological vertex link.

This does not establish singular-chain boundary compatibility
or a homology comparison.
-/
noncomputable def vertexLinkRepresentedEdgePath
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v) :
    C(↥(Set.Icc (0 : ℝ) 1),
      ↥(triangulationTopologicalVertexLink K v)) := by
  let S : Set (Nat → ℝ) :=
    triangulationTopologicalGeometricVertex ''
      (↑({e.lo, e.hi} : Finset Nat) : Set Nat)

  have hlo :
      triangulationTopologicalGeometricVertex e.lo ∈
        convexHull ℝ S := by
    apply subset_convexHull
    exact ⟨e.lo, by simp, rfl⟩

  have hhi :
      triangulationTopologicalGeometricVertex e.hi ∈
        convexHull ℝ S := by
    apply subset_convexHull
    exact ⟨e.hi, by simp, rfl⟩

  let f :
      ↥(Set.Icc (0 : ℝ) 1) →
        ↥(triangulationTopologicalVertexLink K v) :=
    fun t =>
      ⟨
        (1 - t.1) • triangulationTopologicalGeometricVertex e.lo +
          t.1 • triangulationTopologicalGeometricVertex e.hi,
        by
          have hseg :
              (1 - t.1) • triangulationTopologicalGeometricVertex e.lo +
                  t.1 • triangulationTopologicalGeometricVertex e.hi ∈
                segment ℝ
                  (triangulationTopologicalGeometricVertex e.lo)
                  (triangulationTopologicalGeometricVertex e.hi) := by
            rw [segment_eq_image]
            exact ⟨t.1, t.2, rfl⟩
          exact
            (vertexLinkRepresentedEdge_convexHull_subset K v e he)
              ((convex_convexHull ℝ S).segment_subset hlo hhi hseg)
      ⟩

  exact ⟨f, by
    apply Continuous.subtype_mk
    fun_prop⟩

end Poincare
