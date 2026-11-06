import Poincare.VertexLinkDisjointEdgeIntersection
import Poincare.TriangulationTopologicalVertexLink

open Set

namespace Poincare

/--
Every represented vertex-link edge has its canonical
geometric realization contained in the actual
topological vertex-link realization.

No spherical-link or planarity assumption is used.
-/
theorem vertexLinkRepresentedEdge_convexHull_subset
    (K : Triangulation)
    (v : Nat)
    (e : LinkEdge)
    (he : e.RepresentedAt K v) :
    convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑({e.lo, e.hi} : Finset Nat) : Set Nat))
      ⊆ triangulationTopologicalVertexLink K v := by
  obtain ⟨σ, hσ, hσe⟩ := he
  have hsubset :
      (triangulationTopologicalGeometricVertex ''
        (↑({e.lo, e.hi} : Finset Nat) : Set Nat))
        ⊆
      (triangulationTopologicalGeometricVertex ''
        (↑σ.verts.toFinset : Set Nat)) := by
    rintro p ⟨x, hx, rfl⟩
    simp only [
      Finset.mem_coe,
      Finset.mem_insert,
      Finset.mem_singleton
    ] at hx
    rcases hx with rfl | rfl
    · exact ⟨e.lo, List.mem_toFinset.mpr hσe.1, rfl⟩
    · exact ⟨e.hi, List.mem_toFinset.mpr hσe.2, rfl⟩
  intro p hp
  apply (mem_triangulationTopologicalVertexLink_iff K v p).2
  exact ⟨σ, hσ, (convexHull_mono hsubset) hp⟩

end Poincare
