import Poincare.TriangulationTopologicalManifoldVertexLinkStarConnectedness
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Clopen

open Set

namespace Poincare

private theorem List.two_le_length_of_distinct_mem
    {α : Type} {l : List α} {x y : α}
    (hxy : x ≠ y) (hx : x ∈ l) (hy : y ∈ l) :
    2 ≤ l.length := by
  cases l with
  | nil => simp at hx
  | cons a l =>
      cases l with
      | nil =>
          simp at hx hy
          subst x
          subst y
          exact (hxy rfl).elim
      | cons b l =>
          simp

private theorem vertexLinkAdjacent_of_starAdjacent
    (K : Triangulation) (v x : Nat) {σ ρ : LinkTriangle}
    (h : VertexLinkStarAdjacent K v x σ ρ) :
    VertexLinkAdjacent K v σ ρ := by
  rcases h with ⟨hσstar, hρstar, y, hyx, hyσ, hyρ⟩
  have hσ := (mem_vertexLinkStarTriangles_iff K v x σ).1 hσstar
  have hρ := (mem_vertexLinkStarTriangles_iff K v x ρ).1 hρstar
  refine ⟨hσ.1, hρ.1, Or.inl ?_⟩
  unfold LinkTriangle.SharesEdge LinkTriangle.commonVertexCount
  apply List.two_le_length_of_distinct_mem (Ne.symm hyx)
  · simp [hσ.2, hρ.2]
  · simp [hyσ, hyρ]

private theorem linkTriangleFace_inter_eq_commonFace_global
    (σ ρ : LinkTriangle) :
    convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑σ.verts.toFinset : Set Nat)) ∩
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑ρ.verts.toFinset : Set Nat)) =
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑(σ.verts.toFinset ∩ ρ.verts.toFinset) : Set Nat)) := by
  classical
  have hlin : LinearIndependent ℝ triangulationTopologicalGeometricVertex :=
    Pi.linearIndependent_single_one Nat ℝ
  have haff : AffineIndependent ℝ
      ((↑) :
        (↑(σ.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
          ρ.verts.toFinset.image triangulationTopologicalGeometricVertex) :
            Set (Nat → ℝ)) → Nat → ℝ) :=
    hlin.affineIndependent.range.mono (by
      intro z hz
      change z ∈ σ.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
        ρ.verts.toFinset.image triangulationTopologicalGeometricVertex at hz
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

/-- In an honest topological three-manifold, connectedness of the realized
vertex link together with connected represented vertex stars upgrades to the
combinatorial edge-adjacency connectivity required by the descent machinery. -/
theorem ClosedTriangulationCore.vertexLinkConnected_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat} (hv : v ∈ vertexSupport K) :
    VertexLinkConnected K v := by
  classical
  have htop : IsConnected (triangulationTopologicalVertexLink K v) :=
    triangulationTopologicalVertexLink_isConnected_of_topologicalThreeManifold
      K hcore hM hv
  have hlocal : VertexLinkLocallyConnected K v :=
    vertexLinksLocallyConnected_of_topologicalThreeManifold K hcore hM v hv

  intro σ hσ ρ hρ
  by_contra hnpath

  let face : LinkTriangle → Set (Nat → ℝ) := fun τ ↦
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑τ.verts.toFinset : Set Nat))
  let reachable : LinkTriangle → Prop := fun τ ↦
    Relation.ReflTransGen (VertexLinkAdjacent K v) σ τ
  let A : Set (Nat → ℝ) :=
    ⋃ (τ : {t : LinkTriangle // t ∈ vertexLinkTriangles K v})
      (_ : reachable τ.1), face τ.1
  let B : Set (Nat → ℝ) :=
    ⋃ (τ : {t : LinkTriangle // t ∈ vertexLinkTriangles K v})
      (_ : ¬ reachable τ.1), face τ.1

  have hAclosed : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro τ
    apply isClosed_iUnion_of_finite
    intro _
    exact (Set.toFinite _).isClosed_convexHull ℝ

  have hBclosed : IsClosed B := by
    apply isClosed_iUnion_of_finite
    intro τ
    apply isClosed_iUnion_of_finite
    intro _
    exact (Set.toFinite _).isClosed_convexHull ℝ

  have hcover : triangulationTopologicalVertexLink K v ⊆ A ∪ B := by
    intro p hp
    obtain ⟨τ, hτ, hpτ⟩ :=
      (mem_triangulationTopologicalVertexLink_iff K v p).1 hp
    by_cases hr : reachable τ
    · left
      exact Set.mem_iUnion_of_mem ⟨τ, hτ⟩
        (Set.mem_iUnion_of_mem hr hpτ)
    · right
      exact Set.mem_iUnion_of_mem ⟨τ, hτ⟩
        (Set.mem_iUnion_of_mem hr hpτ)

  have starPath_to_linkPath :
      ∀ {x a b : Nat}, True := by
    intro x a b
    trivial

  have liftStarPath :
      ∀ {x : Nat} {a b : LinkTriangle},
        Relation.ReflTransGen (VertexLinkStarAdjacent K v x) a b →
        Relation.ReflTransGen (VertexLinkAdjacent K v) a b := by
    intro x a b hpath
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
        exact Relation.ReflTransGen.tail ih
          (vertexLinkAdjacent_of_starAdjacent K v x hstep)

  have hcross : triangulationTopologicalVertexLink K v ∩ (A ∩ B) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hpLink, hpA, hpB⟩
    simp only [A, B, Set.mem_iUnion] at hpA hpB
    obtain ⟨τ, hτReach, hpτ⟩ := hpA
    obtain ⟨υ, hυNot, hpυ⟩ := hpB

    have hpCommon :
        p ∈ convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑(τ.1.verts.toFinset ∩ υ.1.verts.toFinset) : Set Nat)) := by
      rw [← linkTriangleFace_inter_eq_commonFace_global τ.1 υ.1]
      exact ⟨hpτ, hpυ⟩

    have hcommon : (τ.1.verts.toFinset ∩ υ.1.verts.toFinset).Nonempty := by
      by_contra hnone
      have hempty : τ.1.verts.toFinset ∩ υ.1.verts.toFinset = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnone
      rw [hempty] at hpCommon
      simpa using hpCommon

    obtain ⟨x, hx⟩ := hcommon
    have hxτ : x ∈ τ.1.verts :=
      List.mem_toFinset.mp (Finset.mem_inter.mp hx).1
    have hxυ : x ∈ υ.1.verts :=
      List.mem_toFinset.mp (Finset.mem_inter.mp hx).2
    have hxrep : VertexLinkVertexRepresented K v x :=
      ⟨τ.1, τ.2, hxτ⟩
    have hτstar : τ.1 ∈ vertexLinkStarTriangles K v x :=
      (mem_vertexLinkStarTriangles_iff K v x τ.1).2 ⟨τ.2, hxτ⟩
    have hυstar : υ.1 ∈ vertexLinkStarTriangles K v x :=
      (mem_vertexLinkStarTriangles_iff K v x υ.1).2 ⟨υ.2, hxυ⟩
    have hstar :
        Relation.ReflTransGen (VertexLinkStarAdjacent K v x) τ.1 υ.1 :=
      hlocal x hxrep τ.1 hτstar υ.1 hυstar
    have hlink : Relation.ReflTransGen (VertexLinkAdjacent K v) τ.1 υ.1 :=
      liftStarPath hstar
    exact hυNot (Relation.ReflTransGen.trans hτReach hlink)

  have hone :=
    (isPreconnected_iff_subset_of_disjoint_closed.mp htop.isPreconnected)
      A B hAclosed hBclosed hcover hcross

  have hpσ :
      triangulationTopologicalGeometricVertex σ.v0 ∈
        triangulationTopologicalVertexLink K v := by
    exact (mem_triangulationTopologicalVertexLink_iff K v _).2
      ⟨σ, hσ, by
        apply subset_convexHull
        exact ⟨σ.v0, by simp [LinkTriangle.verts], rfl⟩⟩

  have hpρ :
      triangulationTopologicalGeometricVertex ρ.v0 ∈
        triangulationTopologicalVertexLink K v := by
    exact (mem_triangulationTopologicalVertexLink_iff K v _).2
      ⟨ρ, hρ, by
        apply subset_convexHull
        exact ⟨ρ.v0, by simp [LinkTriangle.verts], rfl⟩⟩

  have hpσA : triangulationTopologicalGeometricVertex σ.v0 ∈ A := by
    exact Set.mem_iUnion_of_mem ⟨σ, hσ⟩
      (Set.mem_iUnion_of_mem Relation.ReflTransGen.refl (by
        apply subset_convexHull
        exact ⟨σ.v0, by simp [LinkTriangle.verts], rfl⟩))

  have hpρB : triangulationTopologicalGeometricVertex ρ.v0 ∈ B := by
    exact Set.mem_iUnion_of_mem ⟨ρ, hρ⟩
      (Set.mem_iUnion_of_mem hnpath (by
        apply subset_convexHull
        exact ⟨ρ.v0, by simp [LinkTriangle.verts], rfl⟩))

  rcases hone with hlinkA | hlinkB
  · have hpρA := hlinkA hpρ
    have hbad : triangulationTopologicalGeometricVertex ρ.v0 ∈
        triangulationTopologicalVertexLink K v ∩ (A ∩ B) :=
      ⟨hpρ, hpρA, hpρB⟩
    rw [hcross] at hbad
    exact hbad
  · have hpσB := hlinkB hpσ
    have hbad : triangulationTopologicalGeometricVertex σ.v0 ∈
        triangulationTopologicalVertexLink K v ∩ (A ∩ B) :=
      ⟨hpσ, hpσA, hpσB⟩
    rw [hcross] at hbad
    exact hbad

end Poincare
