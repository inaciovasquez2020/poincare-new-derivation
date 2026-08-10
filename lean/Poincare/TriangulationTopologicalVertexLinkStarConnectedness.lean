import Poincare.TriangulationTopologicalManifoldVertexLinkConnectedness
import Poincare.TriangulationTopologicalGeometricIntersections
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Clopen

open Set

namespace Poincare

noncomputable def triangulationTopologicalVertexLinkStar
    (K : Triangulation) (v x : Nat) : Set (Nat → ℝ) :=
  ⋃ (sigma : LinkTriangle) (_ : sigma ∈ vertexLinkStarTriangles K v x),
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑sigma.verts.toFinset : Set Nat))

theorem mem_triangulationTopologicalVertexLinkStar_iff
    (K : Triangulation) (v x : Nat) (p : Nat → ℝ) :
    p ∈ triangulationTopologicalVertexLinkStar K v x ↔
      ∃ sigma : LinkTriangle,
        sigma ∈ vertexLinkStarTriangles K v x ∧
        p ∈ convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑sigma.verts.toFinset : Set Nat)) := by
  simp [triangulationTopologicalVertexLinkStar]

theorem triangulationTopologicalVertexLinkStar_subset_vertexLink
    (K : Triangulation) (v x : Nat) :
    triangulationTopologicalVertexLinkStar K v x ⊆
      triangulationTopologicalVertexLink K v := by
  intro p hp
  obtain ⟨sigma, hsigma, hp⟩ :=
    (mem_triangulationTopologicalVertexLinkStar_iff K v x p).1 hp
  exact (mem_triangulationTopologicalVertexLink_iff K v p).2
    ⟨sigma, (mem_vertexLinkStarTriangles_iff K v x sigma).1 hsigma |>.1, hp⟩

noncomputable def triangulationTopologicalPuncturedVertexLinkStar
    (K : Triangulation) (v x : Nat) : Set (Nat → ℝ) :=
  triangulationTopologicalVertexLinkStar K v x \
    {triangulationTopologicalGeometricVertex x}

private theorem LinkTriangle.exists_mem_ne_of_nodup
    (sigma : LinkTriangle) (x : Nat)
    (hnodup : sigma.verts.Nodup) (hx : x ∈ sigma.verts) :
    ∃ y ∈ sigma.verts, y ≠ x := by
  rcases sigma with ⟨a, b, c⟩
  simp [LinkTriangle.verts] at hnodup hx ⊢
  rcases hx with rfl | rfl | rfl <;> omega

theorem exists_geometricVertex_mem_puncturedVertexLinkStar_of_mem
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v x : Nat) {sigma : LinkTriangle}
    (hsigma : sigma ∈ vertexLinkStarTriangles K v x) :
    ∃ y ∈ sigma.verts,
      y ≠ x ∧
      triangulationTopologicalGeometricVertex y ∈
        triangulationTopologicalPuncturedVertexLinkStar K v x := by
  have hsigmaLink := (mem_vertexLinkStarTriangles_iff K v x sigma).1 hsigma
  obtain ⟨y, hy, hyx⟩ := LinkTriangle.exists_mem_ne_of_nodup sigma x
    (vertexLinkTriangles_triangle_nodup K hcore v sigma hsigmaLink.1) hsigmaLink.2
  refine ⟨y, hy, hyx, ?_, ?_⟩
  · apply (mem_triangulationTopologicalVertexLinkStar_iff K v x _).2
    refine ⟨sigma, hsigma, ?_⟩
    apply subset_convexHull
    exact ⟨y, List.mem_toFinset.mpr hy, rfl⟩
  · exact (Pi.linearIndependent_single_one Nat ℝ).injective.ne hyx

private theorem linkTriangleFace_inter_eq_commonFace
    (sigma rho : LinkTriangle) :
    convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑sigma.verts.toFinset : Set Nat)) ∩
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑rho.verts.toFinset : Set Nat)) =
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑(sigma.verts.toFinset ∩ rho.verts.toFinset) : Set Nat)) := by
  classical
  have hlin : LinearIndependent ℝ triangulationTopologicalGeometricVertex :=
    Pi.linearIndependent_single_one Nat ℝ
  have haff : AffineIndependent ℝ
      ((↑) :
        (↑(sigma.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
          rho.verts.toFinset.image triangulationTopologicalGeometricVertex) :
            Set (Nat → ℝ)) → Nat → ℝ) :=
    hlin.affineIndependent.range.mono (by
      intro z hz
      change z ∈ sigma.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
        rho.verts.toFinset.image triangulationTopologicalGeometricVertex at hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
        exact Set.mem_range_self _
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
        exact Set.mem_range_self _)
  rw [← Finset.coe_image, ← Finset.coe_image, ← Finset.coe_image]
  rw [← haff.convexHull_inter']
  congr 2
  rw [← Finset.coe_inter]
  exact congrArg (fun s : Finset (Nat → ℝ) => (↑s : Set (Nat → ℝ)))
    (Finset.image_inter _ _ hlin.injective).symm

theorem vertexLinkStarAdjacent_of_punctured_face_inter_nonempty
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v x : Nat) {sigma rho : LinkTriangle}
    (hsigma : sigma ∈ vertexLinkStarTriangles K v x)
    (hrho : rho ∈ vertexLinkStarTriangles K v x)
    (hinter :
      ((convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑sigma.verts.toFinset : Set Nat)) ∩
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑rho.verts.toFinset : Set Nat))) \
        {triangulationTopologicalGeometricVertex x}).Nonempty) :
    VertexLinkStarAdjacent K v x sigma rho := by
  classical
  obtain ⟨p, hpinter, hpne⟩ := hinter
  rw [linkTriangleFace_inter_eq_commonFace] at hpinter
  refine ⟨hsigma, hrho, ?_⟩
  by_contra hcommon
  push Not at hcommon
  have hsubset : sigma.verts.toFinset ∩ rho.verts.toFinset ⊆ {x} := by
    intro y hy
    simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton] at hy ⊢
    by_contra hyx
    exact hcommon y hyx hy.1 hy.2
  have hpSingleton : p ∈ convexHull ℝ {triangulationTopologicalGeometricVertex x} := by
    apply convexHull_mono ?_ hpinter
    rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_singleton_iff]
    congr
    exact Finset.mem_singleton.mp (hsubset hy)
  have : p = triangulationTopologicalGeometricVertex x := by
    simpa using hpSingleton
  exact hpne this

theorem vertexLinkStarAdjacent_iff_punctured_face_inter_nonempty
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v x : Nat) {sigma rho : LinkTriangle}
    (hsigma : sigma ∈ vertexLinkStarTriangles K v x)
    (hrho : rho ∈ vertexLinkStarTriangles K v x) :
    VertexLinkStarAdjacent K v x sigma rho ↔
      ((convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑sigma.verts.toFinset : Set Nat)) ∩
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑rho.verts.toFinset : Set Nat))) \
        {triangulationTopologicalGeometricVertex x}).Nonempty := by
  constructor
  · rintro ⟨_, _, y, hyx, hysigma, hyrho⟩
    refine ⟨triangulationTopologicalGeometricVertex y, ⟨?_, ?_⟩, ?_⟩
    · apply subset_convexHull
      exact ⟨y, List.mem_toFinset.mpr hysigma, rfl⟩
    · apply subset_convexHull
      exact ⟨y, List.mem_toFinset.mpr hyrho, rfl⟩
    · exact (Pi.linearIndependent_single_one Nat ℝ).injective.ne hyx
  · exact vertexLinkStarAdjacent_of_punctured_face_inter_nonempty
      K hcore v x hsigma hrho

theorem vertexLinkStarConnected_of_puncturedRealization_isConnected
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v x : Nat) (hrep : VertexLinkVertexRepresented K v x)
    (hconn : IsConnected
      (triangulationTopologicalPuncturedVertexLinkStar K v x)) :
    VertexLinkStarConnected K v x := by
  classical
  intro sigma hsigma rho hrho
  by_contra hnpath
  let face : LinkTriangle → Set (Nat → ℝ) := fun tau ↦
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑tau.verts.toFinset : Set Nat))
  let reachable : LinkTriangle → Prop := fun tau ↦
    Relation.ReflTransGen (VertexLinkStarAdjacent K v x) sigma tau
  let A : Set (Nat → ℝ) :=
    ⋃ (tau : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x})
      (_ : reachable tau.1), face tau.1
  let B : Set (Nat → ℝ) :=
    ⋃ (tau : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x})
      (_ : ¬ reachable tau.1), face tau.1
  have hAclosed : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro tau
    apply isClosed_iUnion_of_finite
    intro _
    exact (Set.toFinite _).isClosed_convexHull ℝ
  have hBclosed : IsClosed B := by
    apply isClosed_iUnion_of_finite
    intro tau
    apply isClosed_iUnion_of_finite
    intro _
    exact (Set.toFinite _).isClosed_convexHull ℝ
  have hcover : triangulationTopologicalPuncturedVertexLinkStar K v x ⊆ A ∪ B := by
    rintro p ⟨hp, hpne⟩
    obtain ⟨tau, htau, hptau⟩ :=
      (mem_triangulationTopologicalVertexLinkStar_iff K v x p).1 hp
    by_cases hr : reachable tau
    · left; exact Set.mem_iUnion_of_mem ⟨tau, htau⟩ (Set.mem_iUnion_of_mem hr hptau)
    · right; exact Set.mem_iUnion_of_mem ⟨tau, htau⟩ (Set.mem_iUnion_of_mem hr hptau)
  have hcross : triangulationTopologicalPuncturedVertexLinkStar K v x ∩ (A ∩ B) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    rcases hp with ⟨⟨hpstar, hpne⟩, hpA, hpB⟩
    simp only [A, B, Set.mem_iUnion] at hpA hpB
    obtain ⟨tau, htauReach, hptau⟩ := hpA
    obtain ⟨upsilon, hupsilonNot, hpupsilon⟩ := hpB
    have hadj := vertexLinkStarAdjacent_of_punctured_face_inter_nonempty
      K hcore v x tau.2 upsilon.2
      ⟨p, ⟨hptau, hpupsilon⟩, hpne⟩
    exact hupsilonNot (Relation.ReflTransGen.tail htauReach hadj)
  have hone := (isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected)
    A B hAclosed hBclosed hcover hcross
  obtain ⟨ysigma, _, _, hysigma⟩ :=
    exists_geometricVertex_mem_puncturedVertexLinkStar_of_mem K hcore v x hsigma
  obtain ⟨yrho, _, _, hyrho⟩ :=
    exists_geometricVertex_mem_puncturedVertexLinkStar_of_mem K hcore v x hrho
  rcases hone with hPA | hPB
  · have hyrhoB : triangulationTopologicalGeometricVertex yrho ∈ B := by
      apply Set.mem_iUnion_of_mem ⟨rho, hrho⟩
      apply Set.mem_iUnion_of_mem hnpath
      apply subset_convexHull
      exact ⟨yrho, List.mem_toFinset.mpr ‹yrho ∈ rho.verts›, rfl⟩
    have : triangulationTopologicalGeometricVertex yrho ∈
        triangulationTopologicalPuncturedVertexLinkStar K v x ∩ (A ∩ B) :=
      ⟨hyrho, hPA hyrho, hyrhoB⟩
    rw [hcross] at this
    exact this
  · have hysigmaA : triangulationTopologicalGeometricVertex ysigma ∈ A := by
      exact Set.mem_iUnion_of_mem ⟨sigma, hsigma⟩
        (Set.mem_iUnion_of_mem Relation.ReflTransGen.refl (by
          apply subset_convexHull
          exact ⟨ysigma, List.mem_toFinset.mpr ‹ysigma ∈ sigma.verts›, rfl⟩))
    have : triangulationTopologicalGeometricVertex ysigma ∈
        triangulationTopologicalPuncturedVertexLinkStar K v x ∩ (A ∩ B) :=
      ⟨hysigma, hysigmaA, hPB hysigma⟩
    rw [hcross] at this
    exact this

theorem vertexLinkLocallyConnected_of_puncturedStars_isConnected
    (K : Triangulation) (hcore : ClosedTriangulationCore K) (v : Nat)
    (hgeom : ∀ x : Nat, VertexLinkVertexRepresented K v x →
      IsConnected (triangulationTopologicalPuncturedVertexLinkStar K v x)) :
    VertexLinkLocallyConnected K v := by
  intro x hrep
  exact vertexLinkStarConnected_of_puncturedRealization_isConnected
    K hcore v x hrep (hgeom x hrep)

end Poincare
