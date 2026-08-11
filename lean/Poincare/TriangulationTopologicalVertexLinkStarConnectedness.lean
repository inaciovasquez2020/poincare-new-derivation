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

/-- Barycentric characterization of the apex in a represented vertex-link
star.  In particular, the apex coordinate lies in the unit interval and can
equal one only at the represented apex itself. -/
theorem triangulationTopologicalVertexLinkStar_apex_coordinate
    (K : Triangulation) (v x : Nat) {q : Nat → ℝ}
    (hq : q ∈ triangulationTopologicalVertexLinkStar K v x) :
    0 ≤ q x ∧ q x ≤ 1 ∧
      (q x = 1 ↔ q = triangulationTopologicalGeometricVertex x) := by
  classical
  obtain ⟨sigma, hsigma, hqsigma⟩ :=
    (mem_triangulationTopologicalVertexLinkStar_iff K v x q).1 hq
  let F := sigma.verts.toFinset
  have hxF : x ∈ F := List.mem_toFinset.mpr
    ((mem_vertexLinkStarTriangles_iff K v x sigma).1 hsigma).2
  have hnonneg (j : Nat) : 0 ≤ q j := by
    apply convexHull_min _ (convex_halfSpace_ge
      ⟨fun a b ↦ rfl, fun r a ↦ rfl⟩ (0 : ℝ)) hqsigma
    rintro _ ⟨i, _hi, rfl⟩
    simp [triangulationTopologicalGeometricVertex, Pi.single_apply]
    split <;> norm_num
  have hsum : ∑ j ∈ F, q j = 1 := by
    apply convexHull_min _ (convex_hyperplane
      ⟨fun a b ↦ by simp [Finset.sum_add_distrib],
        fun r a ↦ by simp [Finset.mul_sum]⟩ (1 : ℝ)) hqsigma
    rintro _ ⟨i, hi, rfl⟩
    change ∑ j ∈ F, triangulationTopologicalGeometricVertex i j = 1
    rw [Finset.sum_eq_single i]
    · simp [triangulationTopologicalGeometricVertex]
    · intro j hj hji
      simp [triangulationTopologicalGeometricVertex, hji]
    · exact fun h ↦ (h hi).elim
  have hle : q x ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ ↦ hnonneg j) hxF
  refine ⟨hnonneg x, hle, ?_⟩
  constructor
  · intro hxone
    funext j
    by_cases hjx : j = x
    · subst j
      simp [hxone, triangulationTopologicalGeometricVertex]
    · have hqj : q j = 0 := by
        by_cases hjF : j ∈ F
        · have hjle : q x + q j ≤ ∑ k ∈ F, q k := by
            rw [← Finset.sum_erase_add _ _ hxF, add_comm]
            apply add_le_add_left
            apply Finset.single_le_sum (fun k _ ↦ hnonneg k)
            simp [hjx, hjF]
          rw [hsum, hxone] at hjle
          exact le_antisymm (by linarith) (hnonneg j)
        · apply convexHull_min _ (convex_hyperplane
            ⟨fun a b ↦ rfl, fun r a ↦ rfl⟩ (0 : ℝ)) hqsigma
          rintro _ ⟨i, hi, rfl⟩
          have hij : i ≠ j := fun h ↦ hjF (h ▸ hi)
          simp [triangulationTopologicalGeometricVertex, hij]
      simp [triangulationTopologicalGeometricVertex, hjx, hqj]
  · rintro rfl
    simp [triangulationTopologicalGeometricVertex]

/-- Away from the represented apex, the complementary apex coordinate is
strictly positive. -/
theorem triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
    (K : Triangulation) (v x : Nat) {q : Nat → ℝ}
    (hq : q ∈ triangulationTopologicalVertexLinkStar K v x)
    (hne : q ≠ triangulationTopologicalGeometricVertex x) :
    0 < 1 - q x := by
  rw [sub_pos]
  exact lt_of_le_of_ne
    (triangulationTopologicalVertexLinkStar_apex_coordinate K v x hq).2.1
    (fun h ↦ hne
      ((triangulationTopologicalVertexLinkStar_apex_coordinate K v x hq).2.2.1
        h))

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
    (K : Triangulation) (_hcore : ClosedTriangulationCore K)
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
    (v x : Nat) (_hrep : VertexLinkVertexRepresented K v x)
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

/-- If the represented transverse star is not connected, its punctured
geometric realization has a nontrivial clopen separation. -/
theorem vertexLinkStar_not_connected_gives_clopen_separation
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v x : Nat) (hrep : VertexLinkVertexRepresented K v x)
    (hnot : ¬ VertexLinkStarConnected K v x) :
    ∃ A B : Set
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x),
      IsClopen A ∧ IsClopen B ∧ A.Nonempty ∧ B.Nonempty ∧
        Disjoint A B ∧ Set.univ = A ∪ B := by
  have hnotConnected :
      ¬ IsConnected
        (triangulationTopologicalPuncturedVertexLinkStar K v x) := by
    intro hconnected
    exact hnot
      (vertexLinkStarConnected_of_puncturedRealization_isConnected
        K hcore v x hrep hconnected)
  have hnonempty :
      (triangulationTopologicalPuncturedVertexLinkStar K v x).Nonempty := by
    obtain ⟨sigma, hsigma, hxsigma⟩ := hrep
    obtain ⟨y, _, _, hy⟩ :=
      exists_geometricVertex_mem_puncturedVertexLinkStar_of_mem
        K hcore v x
          ((mem_vertexLinkStarTriangles_iff K v x sigma).2
            ⟨hsigma, hxsigma⟩)
    exact ⟨triangulationTopologicalGeometricVertex y, hy⟩
  have hnotPreconnected :
      ¬ IsPreconnected
        (Set.univ : Set
          ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) := by
    intro hpreconnected
    apply hnotConnected
    rw [isConnected_iff_connectedSpace]
    exact
      { toPreconnectedSpace := ⟨hpreconnected⟩
        toNonempty := hnonempty.to_subtype }
  simpa using
    (isClopen_univ.not_isPreconnected_iff.mp hnotPreconnected)

/-- A disconnected represented transverse star carries a continuous signed
radial coordinate.  Its sign records the two clopen sides away from the apex,
while its absolute value is the complementary apex coordinate. -/
theorem exists_continuous_signedRadialCoordinate_of_not_starConnected
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v x : Nat) (hrep : VertexLinkVertexRepresented K v x)
    (hnot : ¬ VertexLinkStarConnected K v x) :
    ∃ A B : Set
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x),
      IsClopen A ∧ IsClopen B ∧ A.Nonempty ∧ B.Nonempty ∧
        Disjoint A B ∧ Set.univ = A ∪ B ∧
      ∃ g : ↑(triangulationTopologicalVertexLinkStar K v x) → ℝ,
        Continuous g ∧
        (∀ q, |g q| = 1 - q.1 x) ∧
        (∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
          (⟨q.1, q.2, hq⟩ :
              ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ A →
            g q = 1 - q.1 x) ∧
        (∀ q (hq : q.1 ≠ triangulationTopologicalGeometricVertex x),
          (⟨q.1, q.2, hq⟩ :
              ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ B →
            g q = -(1 - q.1 x)) := by
  classical
  obtain ⟨A, B, hAcl, hBcl, hAne, hBne, hdisj, hcover⟩ :=
    vertexLinkStar_not_connected_gives_clopen_separation
      K hcore v x hrep hnot
  let P := ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)
  let S := ↑(triangulationTopologicalVertexLinkStar K v x)
  let radial : P → ℝ := fun q ↦ 1 - q.1 x
  have hradial : Continuous radial :=
    continuous_const.sub ((continuous_apply x).comp continuous_subtype_val)
  let signed : P → ℝ := fun q ↦ if q ∈ A then radial q else -radial q
  have hsigned : Continuous signed := by
    apply hradial.if
    · intro q hq
      exfalso
      change q ∈ frontier A at hq
      rw [hAcl.frontier_eq] at hq
      exact hq
    · exact hradial.neg
  let g : S → ℝ := fun q ↦
    if hq : q.1 = triangulationTopologicalGeometricVertex x then 0
    else signed ⟨q.1, q.2, hq⟩
  have habs : ∀ q : S, |g q| = 1 - q.1 x := by
    intro q
    simp only [g]
    split_ifs with hq
    · rw [hq]
      simp [triangulationTopologicalGeometricVertex]
    · simp only [signed]
      split_ifs
      · exact abs_of_nonneg
          (sub_nonneg.mpr
            (triangulationTopologicalVertexLinkStar_apex_coordinate K v x q.2).2.1)
      · rw [abs_neg, abs_of_nonneg]
        exact sub_nonneg.mpr
          (triangulationTopologicalVertexLinkStar_apex_coordinate K v x q.2).2.1
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro q
    by_cases hq : q.1 = triangulationTopologicalGeometricVertex x
    · have hgq : g q = 0 := by simp [g, hq]
      rw [continuousAt_iff_punctured_nhds, hgq,
          tendsto_zero_iff_abs_tendsto_zero]
      have hcoord : Filter.Tendsto (fun y : S ↦ 1 - y.1 x)
          (nhdsWithin q {q}ᶜ) (nhds 0) := by
        have hc : Continuous (fun y : S ↦ 1 - y.1 x) :=
          continuous_const.sub
            ((continuous_apply x).comp continuous_subtype_val)
        convert hc.continuousAt.mono_left inf_le_left using 1
        simp [hq, triangulationTopologicalGeometricVertex]
      exact hcoord.congr'
        (Filter.Eventually.of_forall fun y ↦ by
          simpa [Function.comp_apply] using (habs y).symm)
    · let D : Set S := {y | y.1 ≠ triangulationTopologicalGeometricVertex x}
      have hDopen : IsOpen D :=
        (isClosed_eq continuous_subtype_val continuous_const).isOpen_compl
      let toP : D → P := fun y ↦ ⟨y.1.1, y.1.2, y.2⟩
      have htoP : Continuous toP :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hrestrict : Continuous (g ∘ ((↑) : D → S)) := by
        have heq : g ∘ ((↑) : D → S) = signed ∘ toP := by
          funext y
          have hy : y.1.1 ≠ triangulationTopologicalGeometricVertex x := y.2
          simp [g, toP, hy]
        rw [heq]
        exact hsigned.comp htoP
      let dq : D := ⟨q, hq⟩
      simpa [dq] using
        (hDopen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
          (hrestrict.continuousAt (x := dq)))
  refine ⟨A, B, hAcl, hBcl, hAne, hBne, hdisj, hcover, g, hg, habs, ?_, ?_⟩
  · intro q hq hqA
    simp [g, hq, signed, hqA, radial]
  · intro q hq hqB
    have hqA :
        (⟨q.1, q.2, hq⟩ :
            ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∉ A := by
      intro hmem
      exact Set.disjoint_left.1 hdisj hmem hqB
    simp [g, hq, signed, hqA, radial]

/-- A clopen side of the punctured represented link star contains every
positive radial contraction of each of its points toward the apex.  This is
the component-control lemma used by the circle inclusion in the edge local
model. -/
theorem IsClopen.vertexLinkStar_radial_mem
    (K : Triangulation) (v x : Nat)
    {A : Set ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)}
    (hA : IsClopen A)
    (q : ↑(triangulationTopologicalPuncturedVertexLinkStar K v x))
    (hqA : q ∈ A) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    let p := (AffineMap.lineMap
      (triangulationTopologicalGeometricVertex x) q.1) c
    ∃ hp : p ∈ triangulationTopologicalVertexLinkStar K v x,
      (⟨p, hp, by
        intro heq
        have heq' : p = triangulationTopologicalGeometricVertex x := by
          simpa only [Set.mem_singleton_iff] using heq
        have hcoord := congrFun heq' x
        have hradial :=
          triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
            K v x q.2.1 q.2.2
        dsimp [p] at hcoord
        simp [AffineMap.lineMap_apply,
          triangulationTopologicalGeometricVertex] at hcoord
        rcases hcoord with hc | hq
        · exact (ne_of_gt hc0) hc
        · linarith⟩ :
        ↑(triangulationTopologicalPuncturedVertexLinkStar K v x)) ∈ A := by
  classical
  dsimp only
  obtain ⟨sigma, hsigma, hqsigma⟩ :=
    (mem_triangulationTopologicalVertexLinkStar_iff K v x q.1).1 q.2.1
  have hxverts : x ∈ sigma.verts :=
    (mem_vertexLinkStarTriangles_iff K v x sigma).1 hsigma |>.2
  have hxbody : triangulationTopologicalGeometricVertex x ∈
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑sigma.verts.toFinset : Set Nat)) := by
    apply subset_convexHull
    exact ⟨x, List.mem_toFinset.mpr hxverts, rfl⟩
  have radial_mem (s : ↑(Set.Ioc (0 : ℝ) 1)) :
      (AffineMap.lineMap
        (triangulationTopologicalGeometricVertex x) q.1) s.1 ∈
          triangulationTopologicalVertexLinkStar K v x := by
    apply (mem_triangulationTopologicalVertexLinkStar_iff K v x _).2
    exact ⟨sigma, hsigma,
      (convex_convexHull ℝ _).lineMap_mem hxbody hqsigma ⟨s.2.1.le, s.2.2⟩⟩
  have radial_ne (s : ↑(Set.Ioc (0 : ℝ) 1)) :
      (AffineMap.lineMap
        (triangulationTopologicalGeometricVertex x) q.1) s.1 ≠
          triangulationTopologicalGeometricVertex x := by
    intro heq
    have hcoord := congrFun heq x
    have hradial :=
      triangulationTopologicalVertexLinkStar_one_sub_coordinate_pos
        K v x q.2.1 q.2.2
    simp [AffineMap.lineMap_apply,
      triangulationTopologicalGeometricVertex] at hcoord
    rcases hcoord with hs | hq
    · exact (ne_of_gt s.2.1) hs
    · linarith
  let f : ↑(Set.Ioc (0 : ℝ) 1) →
      ↑(triangulationTopologicalPuncturedVertexLinkStar K v x) := fun s ↦
    ⟨(AffineMap.lineMap
      (triangulationTopologicalGeometricVertex x) q.1) s.1,
      radial_mem s, radial_ne s⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact AffineMap.lineMap_continuous.comp continuous_subtype_val
  letI : PreconnectedSpace ↑(Set.Ioc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Ioc
  have hpre : IsClopen (f ⁻¹' A) := hA.preimage hf
  have hone : (1 : ↑(Set.Ioc (0 : ℝ) 1)) ∈ f ⁻¹' A := by
    simpa [f, AffineMap.lineMap_apply] using hqA
  have hall : f ⁻¹' A = Set.univ := hpre.eq_univ ⟨1, hone⟩
  let sc : ↑(Set.Ioc (0 : ℝ) 1) := ⟨c, hc0, hc1⟩
  refine ⟨radial_mem sc, ?_⟩
  have : sc ∈ f ⁻¹' A := by rw [hall]; trivial
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
