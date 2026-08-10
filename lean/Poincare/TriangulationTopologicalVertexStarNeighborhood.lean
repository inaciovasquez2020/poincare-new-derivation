import Poincare.TriangulationTopologicalVertexStarConeHomeomorph
import Poincare.Move23ActualRegions
import Poincare.TriangulationTopologicalSimplyConnected

open Set Filter

namespace Poincare

/-- A point of a represented tetrahedron has zero coordinate at every label
absent from that tetrahedron. -/
theorem triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
    (tau : Tet) (v : Nat) (hv : v ∉ tau.verts) {p : Nat → ℝ}
    (hp : p ∈ triangulationTopologicalTetBody tau) :
    p v = 0 := by
  classical
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
  rintro _ ⟨y, hy, rfl⟩
  have hyv : y ≠ v := by
    intro hyv
    subst y
    exact hv (List.mem_toFinset.mp hy)
  simp [triangulationTopologicalGeometricVertex, hyv]

/-- Positive apex coordinate forces a point of the full realization into the
represented vertex star. -/
theorem triangulationTopologicalVertexStar_mem_of_mem_space_of_coordinate_pos
    (K : Triangulation) (v : Nat) {p : Nat → ℝ}
    (hp : p ∈ (triangulationTopologicalGeometricComplex K).space)
    (hpv : 0 < p v) :
    p ∈ triangulationTopologicalVertexStar K v := by
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion] at hp
  simp only [mem_iUnion] at hp
  obtain ⟨tau, htau, hpbody⟩ := hp
  by_cases hv : v ∈ tau.verts
  · exact (mem_triangulationTopologicalVertexStar_iff K v p).2
      ⟨tau, htau, hv, hpbody⟩
  · have hz := triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
      tau v hv hpbody
    linarith

/-- A represented vertex belonging to the combinatorial support is a point of
the full topology-bearing realization. -/
theorem triangulationTopologicalGeometricVertex_mem_space_of_mem_vertexSupport
    (K : Triangulation) {v : Nat} (hv : v ∈ vertexSupport K) :
    triangulationTopologicalGeometricVertex v ∈
      (triangulationTopologicalGeometricComplex K).space := by
  rw [mem_vertexSupport_iff] at hv
  simp only [allVerts, List.mem_flatMap] at hv
  obtain ⟨tau, htau, hvtau⟩ := hv
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  simp only [mem_iUnion]
  refine ⟨tau, htau, subset_convexHull ℝ _ ?_⟩
  exact ⟨v, List.mem_toFinset.mpr hvtau, rfl⟩

/-- The represented vertex, regarded as a point of the full carrier. -/
noncomputable def triangulationTopologicalCarrierVertex
    (K : Triangulation) (v : Nat) (hv : v ∈ vertexSupport K) :
    triangulationTopologicalGeometricCarrier K :=
  ⟨triangulationTopologicalGeometricVertex v,
    triangulationTopologicalGeometricVertex_mem_space_of_mem_vertexSupport K hv⟩

@[simp] theorem triangulationTopologicalCarrierVertex_coordinate
    (K : Triangulation) (v : Nat) (hv : v ∈ vertexSupport K) :
    (triangulationTopologicalCarrierVertex K v hv).1 v = 1 := by
  simp [triangulationTopologicalCarrierVertex,
    triangulationTopologicalGeometricVertex]

/-- The coordinate half-space around the represented apex, restricted to the
full triangulation carrier. -/
def triangulationTopologicalTruncatedVertexStarNeighborhood
    (K : Triangulation) (v : Nat) :
    Set (triangulationTopologicalGeometricCarrier K) :=
  {p | (1 / 2 : ℝ) < p.1 v}

theorem triangulationTopologicalTruncatedVertexStarNeighborhood_isOpen
    (K : Triangulation) (v : Nat) :
    IsOpen (triangulationTopologicalTruncatedVertexStarNeighborhood K v) := by
  exact isOpen_Ioi.preimage
    ((continuous_apply v).comp continuous_subtype_val)

theorem triangulationTopologicalCarrierVertex_mem_truncatedVertexStarNeighborhood
    (K : Triangulation) {v : Nat} (hv : v ∈ vertexSupport K) :
    triangulationTopologicalCarrierVertex K v hv ∈
      triangulationTopologicalTruncatedVertexStarNeighborhood K v := by
  simp [triangulationTopologicalTruncatedVertexStarNeighborhood]
  norm_num

theorem triangulationTopologicalTruncatedVertexStarNeighborhood_subset_vertexStar
    (K : Triangulation) (v : Nat) :
    ∀ p : triangulationTopologicalGeometricCarrier K,
      p ∈ triangulationTopologicalTruncatedVertexStarNeighborhood K v →
      p.1 ∈ triangulationTopologicalVertexStar K v := by
  intro p hp
  apply triangulationTopologicalVertexStar_mem_of_mem_space_of_coordinate_pos
    K v p.2
  change (1 / 2 : ℝ) < p.1 v at hp
  linarith

/-- An explicit open carrier neighborhood of the represented vertex contained
in its represented tetrahedral star. -/
theorem triangulationTopologicalVertexStar_mem_nhds_carrierVertex
    (K : Triangulation) {v : Nat} (hv : v ∈ vertexSupport K) :
    ∃ U : Set (triangulationTopologicalGeometricCarrier K),
      IsOpen U ∧
      triangulationTopologicalCarrierVertex K v hv ∈ U ∧
      ∀ p ∈ U, p.1 ∈ triangulationTopologicalVertexStar K v := by
  exact ⟨triangulationTopologicalTruncatedVertexStarNeighborhood K v,
    triangulationTopologicalTruncatedVertexStarNeighborhood_isOpen K v,
    triangulationTopologicalCarrierVertex_mem_truncatedVertexStarNeighborhood K hv,
    triangulationTopologicalTruncatedVertexStarNeighborhood_subset_vertexStar K v⟩

theorem triangulationTopologicalTruncatedVertexStarNeighborhood_mem_nhds
    (K : Triangulation) {v : Nat} (hv : v ∈ vertexSupport K) :
    triangulationTopologicalTruncatedVertexStarNeighborhood K v ∈
      nhds (triangulationTopologicalCarrierVertex K v hv) := by
  exact (triangulationTopologicalTruncatedVertexStarNeighborhood_isOpen K v).mem_nhds
    (triangulationTopologicalCarrierVertex_mem_truncatedVertexStarNeighborhood K hv)

/-- The represented vertex star itself is a neighborhood of its apex in the
full carrier. -/
theorem triangulationTopologicalVertexStarCarrier_mem_nhds
    (K : Triangulation) {v : Nat} (hv : v ∈ vertexSupport K) :
    {p : triangulationTopologicalGeometricCarrier K |
      p.1 ∈ triangulationTopologicalVertexStar K v} ∈
      nhds (triangulationTopologicalCarrierVertex K v hv) := by
  apply Filter.mem_of_superset
    (triangulationTopologicalTruncatedVertexStarNeighborhood_mem_nhds K hv)
  exact triangulationTopologicalTruncatedVertexStarNeighborhood_subset_vertexStar K v

end Poincare
