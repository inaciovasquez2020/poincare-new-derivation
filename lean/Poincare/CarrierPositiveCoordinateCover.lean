import Poincare.TriangulationTopologicalVertexStarNeighborhood

open Set
open scoped BigOperators

namespace Poincare

/-- Honest finite barycentric data for a point in the convex hull of a finite
set of canonical geometric vertices. -/
theorem convexHull_geometricVertex_image_exists_weights
    (F : Finset Nat) (x : Nat → ℝ)
    (hx : x ∈ convexHull ℝ
      (triangulationTopologicalGeometricVertex '' (↑F : Set Nat))) :
    ∃ w : Nat → ℝ,
      (∀ v ∈ F, 0 ≤ w v) ∧
      (∑ v ∈ F, w v = 1) ∧
      ∑ v ∈ F, w v • triangulationTopologicalGeometricVertex v = x := by
  classical
  rw [Set.image_eq_range,
    convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, a, ha0, ha1, hax⟩ := hx
  let w : Nat → ℝ := fun v => if hv : v ∈ F then
    if (⟨v, hv⟩ : ↥F) ∈ s then a ⟨v, hv⟩ else 0 else 0
  have hs : s ⊆ F.attach := by
    intro i hi
    simp
  refine ⟨w, ?_, ?_, ?_⟩
  · intro v hv
    simp only [w, dif_pos hv]
    split
    · apply ha0
      assumption
    · exact le_rfl
  · rw [← Finset.sum_attach]
    simpa [w, Finset.inter_eq_right.mpr hs] using ha1
  · rw [← hax]
    rw [Finset.affineCombination_eq_linear_combination s _ a ha1]
    rw [← Finset.sum_attach]
    simp [w, Finset.inter_eq_right.mpr hs]

/-- Coordinates of a finite canonical barycentric combination are exactly its
labelled coefficients (and vanish off the finite label set). -/
theorem geometricVertex_weighted_sum_coordinate
    (F : Finset Nat) (w : Nat → ℝ) (x : Nat → ℝ)
    (hx : ∑ v ∈ F, w v • triangulationTopologicalGeometricVertex v = x)
    (j : Nat) :
    x j = if j ∈ F then w j else 0 := by
  rw [← hx]
  simp only [Finset.sum_apply]
  by_cases hj : j ∈ F
  · rw [if_pos hj]
    rw [Finset.sum_eq_single j]
    · simp [triangulationTopologicalGeometricVertex]
    · intro b hb hbj
      simp [triangulationTopologicalGeometricVertex, hbj]
    · exact fun h => (h hj).elim
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro b hb
    have hbj : b ≠ j := by rintro rfl; exact hj hb
    simp [triangulationTopologicalGeometricVertex, hbj]

/-- A nonnegative finite family summing to one has a strictly positive member. -/
theorem exists_pos_weight_of_nonneg_sum_one
    (F : Finset Nat) (w : Nat → ℝ)
    (h0 : ∀ v ∈ F, 0 ≤ w v) (h1 : ∑ v ∈ F, w v = 1) :
    ∃ v ∈ F, 0 < w v := by
  by_contra h
  push Not at h
  have hz : ∀ v ∈ F, w v = 0 := by
    intro v hv
    exact le_antisymm (h v hv) (h0 v hv)
  have hsum : ∑ v ∈ F, w v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hz v hv
  linarith

/-- Every carrier point has genuine finite barycentric support inside one
represented tetrahedron. -/
theorem carrier_exists_finite_barycentric_support
    {K : Triangulation}
    (p : triangulationTopologicalGeometricCarrier K) :
    ∃ F : Finset Nat, F.Nonempty ∧
      ∃ tau : Tet, tau ∈ K.tets ∧ F ⊆ tau.verts.toFinset ∧
      ∃ w : Nat → ℝ,
        (∀ v ∈ F, 0 ≤ w v) ∧
        (∑ v ∈ F, w v = 1) ∧
        ∑ v ∈ F, w v • triangulationTopologicalGeometricVertex v = p.1 := by
  obtain ⟨F, hF, ⟨tau, htau, hFtau⟩, hp⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff K p.1).1 p.2
  obtain ⟨w, hw0, hw1, hwp⟩ :=
    convexHull_geometricVertex_image_exists_weights F p.1 hp
  exact ⟨F, hF, tau, htau, hFtau, w, hw0, hw1, hwp⟩

theorem carrier_coordinate_nonneg
    {K : Triangulation}
    (p : triangulationTopologicalGeometricCarrier K) (j : Nat) :
    0 ≤ p.1 j := by
  obtain ⟨F, _, _, _, _, w, hw0, _, hwp⟩ :=
    carrier_exists_finite_barycentric_support p
  rw [geometricVertex_weighted_sum_coordinate F w p.1 hwp j]
  split
  · apply hw0
    assumption
  · exact le_rfl

/-- Every carrier point has a strictly positive coordinate at a represented
vertex. -/
theorem carrier_exists_vertexSupport_coordinate_pos
    {K : Triangulation}
    (p : triangulationTopologicalGeometricCarrier K) :
    ∃ v, v ∈ vertexSupport K ∧ 0 < p.1 v := by
  obtain ⟨F, _, tau, htau, hFtau, w, hw0, hw1, hwp⟩ :=
    carrier_exists_finite_barycentric_support p
  obtain ⟨v, hvF, hwv⟩ := exists_pos_weight_of_nonneg_sum_one F w hw0 hw1
  refine ⟨v, ?_, ?_⟩
  · rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, List.mem_toFinset.mp (hFtau hvF)⟩
  · rw [geometricVertex_weighted_sum_coordinate F w p.1 hwp v, if_pos hvF]
    exact hwv

/-- The open positive-coordinate part of the carrier. -/
def triangulationTopologicalPositiveCoordinate
    (K : Triangulation) (v : Nat) :
    Set (triangulationTopologicalGeometricCarrier K) :=
  {p | 0 < p.1 v}

theorem triangulationTopologicalPositiveCoordinate_isOpen
    (K : Triangulation) (v : Nat) :
    IsOpen (triangulationTopologicalPositiveCoordinate K v) := by
  exact isOpen_Ioi.preimage ((continuous_apply v).comp continuous_subtype_val)

theorem triangulationTopologicalPositiveCoordinate_subset_vertexStar
    (K : Triangulation) (v : Nat) :
    ∀ p ∈ triangulationTopologicalPositiveCoordinate K v,
      p.1 ∈ triangulationTopologicalVertexStar K v := by
  intro p hp
  exact triangulationTopologicalVertexStar_mem_of_mem_space_of_coordinate_pos
    K v p.2 hp

/-- The finitely many positive-coordinate opens indexed by the combinatorial
vertex support cover the whole carrier. -/
theorem triangulationTopologicalPositiveCoordinate_iUnion_eq_univ
    (K : Triangulation) :
    (⋃ v ∈ (vertexSupport K).toFinset,
      triangulationTopologicalPositiveCoordinate K v) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨v, hv, hpv⟩ := carrier_exists_vertexSupport_coordinate_pos p
  simp only [Set.mem_iUnion]
  exact ⟨v, List.mem_toFinset.mpr hv, hpv⟩

/-- Two represented tetrahedral bodies which meet have a common labelled
vertex. -/
theorem triangulationTopologicalTetBody_inter_nonempty_implies_common_vertex
    {tau rho : Tet} {x : Nat → ℝ}
    (hxtau : x ∈ triangulationTopologicalTetBody tau)
    (hxrho : x ∈ triangulationTopologicalTetBody rho) :
    ∃ v, v ∈ tau.verts ∧ v ∈ rho.verts := by
  obtain ⟨w, hw0, hw1, hwx⟩ :=
    convexHull_geometricVertex_image_exists_weights tau.verts.toFinset x hxtau
  obtain ⟨v, hv, hwv⟩ :=
    exists_pos_weight_of_nonneg_sum_one tau.verts.toFinset w hw0 hw1
  have hxv : 0 < x v := by
    rw [geometricVertex_weighted_sum_coordinate tau.verts.toFinset w x hwx v,
      if_pos hv]
    exact hwv
  refine ⟨v, List.mem_toFinset.mp hv, ?_⟩
  by_contra hvrho
  have hz := triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
    rho v hvrho hxrho
  linarith

/-- Round-1 package: the carrier has a finite, support-indexed open cover
subordinate to represented vertex stars, and intersecting tetrahedral bodies
have a common represented vertex. -/
theorem finitePositiveCoordinateOpenStarCover_and_tetBodyOverlap
    (K : Triangulation) :
    (∀ v : Nat,
      IsOpen (triangulationTopologicalPositiveCoordinate K v) ∧
      ∀ p ∈ triangulationTopologicalPositiveCoordinate K v,
        p.1 ∈ triangulationTopologicalVertexStar K v) ∧
    (⋃ v ∈ (vertexSupport K).toFinset,
      triangulationTopologicalPositiveCoordinate K v) = Set.univ ∧
    ∀ (tau rho : Tet) (x : Nat → ℝ),
      tau ∈ K.tets → rho ∈ K.tets →
      x ∈ triangulationTopologicalTetBody tau →
      x ∈ triangulationTopologicalTetBody rho →
      ∃ v, v ∈ tau.verts ∧ v ∈ rho.verts := by
  refine ⟨?_, triangulationTopologicalPositiveCoordinate_iUnion_eq_univ K, ?_⟩
  · intro v
    exact ⟨triangulationTopologicalPositiveCoordinate_isOpen K v,
      triangulationTopologicalPositiveCoordinate_subset_vertexStar K v⟩
  · intro tau rho x _ _ hxtau hxrho
    exact triangulationTopologicalTetBody_inter_nonempty_implies_common_vertex
      hxtau hxrho

end Poincare
