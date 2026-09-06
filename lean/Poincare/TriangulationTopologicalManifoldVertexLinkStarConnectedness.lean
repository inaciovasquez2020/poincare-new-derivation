import Poincare.TriangulationTopologicalEdgeLocalModel
import Poincare.TriangulationTopologicalManifoldPuncturedNeighborhood

open Set Filter

namespace Poincare

/-- In an honest topological three-manifold, every represented transverse
vertex-link star is connected.  A disconnected star would give a circle
retract inside an arbitrarily small punctured chart ball. -/
theorem vertexLinkStarConnected_of_topologicalThreeManifold
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat} (hrep : VertexLinkVertexRepresented K v x) :
    VertexLinkStarConnected K v x := by
  by_contra hnot
  let m := triangulationTopologicalCarrierEdgeMidpoint K v x hrep
  let N := triangulationTopologicalOpenEdgeNeighborhood K v x
  have hN : N ∈ nhds m := by
    exact triangulationTopologicalOpenEdgeNeighborhood_mem_nhds K hcore hrep
  obtain ⟨U, hUopen, hmU, hUN, hUsimply⟩ :=
    triangulationTopological_exists_open_punctured_simplyConnected_neighborhood_sub
      K hM m hN
  obtain ⟨A, B, hAcl, hBcl, hAne, hBne, -, -, g, hg, habs, hgA, hgB⟩ :=
    exists_continuous_signedRadialCoordinate_of_not_starConnected
      K hcore v x hrep hnot
  obtain ⟨qA, hqA, qB, hqB, -, -, -, -⟩ :=
    exists_edgeRadial_opposite_side_witnesses
      K v x A B hAne hBne g hgA hgB
  obtain ⟨δ, hδ0, hδquarter, hδA, hδB, hδU⟩ :=
    exists_edgeRadial_circleScale_carrier_image_subset
      K hcore hrep qA qB U (hUopen.mem_nhds hmU)
  let e :=
    triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier
      K hcore hrep
  let inc := edgeRadialCircleInclusion
    K hrep qA qB δ hδ0 hδquarter hδA hδB
  have hinc : Continuous inc := by
    exact continuous_edgeRadialCircleInclusion
      K hrep qA qB δ hδ0 hδquarter hδA hδB
  let i : C(Circle, ↑(U \ {m})) := ⟨fun z ↦
    ⟨(e (inc z)).1, hδU hδ0 hδquarter hδA hδB z, by
      simp only [mem_singleton_iff]
      intro heq
      have heq' : e (inc z) =
          ⟨m, triangulationTopologicalCarrierEdgeMidpoint_mem_openEdgeNeighborhood
            K hcore hrep⟩ := by
        apply Subtype.ext
        exact heq
      rw [← triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier_midpoint
        K hcore hrep] at heq'
      exact (inc z).2 (e.injective heq')⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (e.continuous.comp
        (continuous_subtype_val.comp hinc))⟩
  let pull : ↑(U \ {m}) →
      ↑({triangulationTopologicalOpenEdgeRadialMidpoint K hrep}ᶜ : Set
        {tq : ↑(Set.Ico (0 : ℝ) 1) ×
            ↑(triangulationTopologicalVertexLink K v) |
          0 < tq.1.1 ∧ 0 < tq.2.1 x}) := fun p ↦
    ⟨e.symm ⟨p.1, hUN p.2.1⟩, by
      simp only [mem_compl_iff, mem_singleton_iff]
      intro heq
      have heq' := congrArg e heq
      rw [e.apply_symm_apply,
        triangulationTopologicalOpenEdgeNeighborhoodHomeomorphRadialLinkCarrier_midpoint
          K hcore hrep] at heq'
      exact p.2.2 (congrArg Subtype.val heq')⟩
  have hpull : Continuous pull := by
    apply Continuous.subtype_mk
    exact e.symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _)
  let r : C(↑(U \ {m}), Circle) := ⟨fun p ↦
    edgeRadialCircleMap K hrep g habs (pull p),
    (continuous_edgeRadialCircleMap K hrep g hg habs).comp hpull⟩
  have hnotSimply : ¬ SimplyConnectedSpace ↑(U \ {m}) :=
    not_simplyConnectedSpace_of_circle_retract i r fun z ↦ by
      have hpullinc : pull (i z) = inc z := by
        apply Subtype.ext
        apply e.injective
        rw [e.apply_symm_apply]
        rfl
      change edgeRadialCircleMap K hrep g habs (pull (i z)) = z
      rw [hpullinc]
      exact edgeRadialCircleMap_comp_edgeRadialCircleInclusion
        K hrep A B hAcl hBcl qA qB hqA hqB g habs hgA hgB
          δ hδ0 hδquarter hδA hδB z
  exact hnotSimply hUsimply

/-- Every supported vertex of an honest topological three-manifold has
connected represented vertex-link stars. -/
theorem vertexLinksLocallyConnected_of_topologicalThreeManifold
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K) :
    VertexLinksLocallyConnected K := by
  intro v _ x hrep
  exact vertexLinkStarConnected_of_topologicalThreeManifold K hcore hM hrep

/-- A local-star adjacency step is already a global edge-adjacency step in the
represented vertex link: the star center and the witnessed noncenter vertex
are two distinct common vertices of the two link triangles. -/
theorem VertexLinkStarAdjacent.vertexLinkAdjacent
    {K : Triangulation} {v x : Nat} {sigma rho : LinkTriangle}
    (h : VertexLinkStarAdjacent K v x sigma rho) :
    VertexLinkAdjacent K v sigma rho := by
  rcases h with ⟨hsigmaStar, hrhoStar, y, hyx, hysigma, hyrho⟩
  have hsigma :=
    (mem_vertexLinkStarTriangles_iff K v x sigma).1 hsigmaStar
  have hrho :=
    (mem_vertexLinkStarTriangles_iff K v x rho).1 hrhoStar
  refine ⟨hsigma.1, hrho.1, Or.inl ?_⟩
  unfold LinkTriangle.SharesEdge LinkTriangle.commonVertexCount
  let l := sigma.verts.eraseDups.filter (fun z => rho.verts.contains z)
  have hxL : x ∈ l := by
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_eraseDups.mpr hsigma.2
    · simpa using hrho.2
  have hyL : y ∈ l := by
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_eraseDups.mpr hysigma
    · simpa using hyrho
  have hn : l.Nodup := by
    exact (eraseDups_nodup_nat sigma.verts).filter _
  have hsub : ({x, y} : Finset Nat) ⊆ l.toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact List.mem_toFinset.mpr hxL
    · exact List.mem_toFinset.mpr hyL
  have hcard_le := Finset.card_le_card hsub
  have hpair : ({x, y} : Finset Nat).card = 2 := by
    simp [Ne.symm hyx]
  have hlcard : l.toFinset.card = l.length :=
    List.toFinset_card_of_nodup hn
  rw [hpair, hlcard] at hcard_le
  exact hcard_le

/-- A connected local star supplies a global edge-adjacency path between any
two represented link triangles in that star. -/
theorem VertexLinkStarConnected.vertexLinkPath
    {K : Triangulation} {v x : Nat}
    (hconnected : VertexLinkStarConnected K v x)
    {sigma rho : LinkTriangle}
    (hsigma : sigma ∈ vertexLinkStarTriangles K v x)
    (hrho : rho ∈ vertexLinkStarTriangles K v x) :
    Relation.ReflTransGen (VertexLinkAdjacent K v) sigma rho := by
  have hpath := hconnected sigma hsigma rho hrho
  exact
    Relation.ReflTransGen.trans_induction_on
      (motive := fun {a b} _ =>
        Relation.ReflTransGen (VertexLinkAdjacent K v) a b)
      hpath
      (fun _ => Relation.ReflTransGen.refl)
      (fun hstep =>
        Relation.ReflTransGen.single
          (VertexLinkStarAdjacent.vertexLinkAdjacent hstep))
      (fun _ _ ih₁ ih₂ =>
        Relation.ReflTransGen.trans ih₁ ih₂)

/-- If two represented link triangles share a vertex, local connectedness at
that vertex upgrades the shared-vertex contact to a global edge-adjacency
path. -/
theorem VertexLinkLocallyConnected.vertexLinkPath_of_commonVertex
    {K : Triangulation} {v x : Nat}
    (hlocal : VertexLinkLocallyConnected K v)
    {sigma rho : LinkTriangle}
    (hsigma : sigma ∈ vertexLinkTriangles K v)
    (hrho : rho ∈ vertexLinkTriangles K v)
    (hxsigma : x ∈ sigma.verts)
    (hxrho : x ∈ rho.verts) :
    Relation.ReflTransGen (VertexLinkAdjacent K v) sigma rho := by
  have hrep : VertexLinkVertexRepresented K v x :=
    ⟨sigma, hsigma, hxsigma⟩
  have hstar : VertexLinkStarConnected K v x :=
    hlocal x hrep
  exact hstar.vertexLinkPath
    ((mem_vertexLinkStarTriangles_iff K v x sigma).2 ⟨hsigma, hxsigma⟩)
    ((mem_vertexLinkStarTriangles_iff K v x rho).2 ⟨hrho, hxrho⟩)

/-- Connectedness of the geometric vertex-link realization, together with
connectedness of every represented vertex star, forces the repository's
stronger edge-adjacency notion of combinatorial vertex-link connectedness. -/
theorem VertexLinkLocallyConnected.vertexLinkConnected_of_geometric_isConnected
    {K : Triangulation} {v : Nat}
    (hlocal : VertexLinkLocallyConnected K v)
    (hconn : IsConnected (triangulationTopologicalVertexLink K v)) :
    VertexLinkConnected K v := by
  classical
  letI : Fintype {tau : LinkTriangle // tau ∈ vertexLinkTriangles K v} :=
    Fintype.ofFinset (vertexLinkTriangles K v).toFinset (by
      intro tau
      exact List.mem_toFinset)
  intro sigma hsigma rho hrho
  by_contra hnpath
  let face : LinkTriangle → Set (Nat → ℝ) := fun tau ↦
    convexHull ℝ
      (triangulationTopologicalGeometricVertex ''
        (↑tau.verts.toFinset : Set Nat))
  let reachable : LinkTriangle → Prop := fun tau ↦
    Relation.ReflTransGen (VertexLinkAdjacent K v) sigma tau
  let A : Set (Nat → ℝ) :=
    ⋃ (tau : {t : LinkTriangle // t ∈ vertexLinkTriangles K v})
      (_ : reachable tau.1), face tau.1
  let B : Set (Nat → ℝ) :=
    ⋃ (tau : {t : LinkTriangle // t ∈ vertexLinkTriangles K v})
      (_ : ¬ reachable tau.1), face tau.1
  have hface_inter (a b : LinkTriangle) :
      face a ∩ face b =
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑(a.verts.toFinset ∩ b.verts.toFinset) : Set Nat)) := by
    have hlin : LinearIndependent ℝ triangulationTopologicalGeometricVertex :=
      Pi.linearIndependent_single_one Nat ℝ
    have haff : AffineIndependent ℝ
        ((↑) :
          (↑(a.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
            b.verts.toFinset.image triangulationTopologicalGeometricVertex) :
              Set (Nat → ℝ)) → Nat → ℝ) :=
      hlin.affineIndependent.range.mono (by
        intro z hz
        change z ∈ a.verts.toFinset.image triangulationTopologicalGeometricVertex ∪
          b.verts.toFinset.image triangulationTopologicalGeometricVertex at hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
          exact Set.mem_range_self _
        · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
          exact Set.mem_range_self _)
    dsimp [face]
    rw [← Finset.coe_image, ← Finset.coe_image, ← Finset.coe_image]
    rw [← haff.convexHull_inter']
    congr 2
    rw [← Finset.coe_inter]
    exact congrArg (fun s : Finset (Nat → ℝ) => (↑s : Set (Nat → ℝ)))
      (Finset.image_inter _ _ hlin.injective).symm
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
  have hcover : triangulationTopologicalVertexLink K v ⊆ A ∪ B := by
    intro p hp
    obtain ⟨tau, htau, hpface⟩ :=
      (mem_triangulationTopologicalVertexLink_iff K v p).1 hp
    change p ∈ face tau at hpface
    by_cases hr : reachable tau
    · left
      exact Set.mem_iUnion_of_mem ⟨tau, htau⟩
        (Set.mem_iUnion_of_mem hr hpface)
    · right
      exact Set.mem_iUnion_of_mem ⟨tau, htau⟩
        (Set.mem_iUnion_of_mem hr hpface)
  have hdisj : A ∩ B = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hpA, hpB⟩
    simp only [A, B, Set.mem_iUnion] at hpA hpB
    obtain ⟨tau, htauReach, hptau⟩ := hpA
    obtain ⟨upsilon, hupsilonNot, hpupsilon⟩ := hpB
    have hinter : p ∈ face tau.1 ∩ face upsilon.1 := ⟨hptau, hpupsilon⟩
    rw [hface_inter tau.1 upsilon.1] at hinter
    have hcommon :
        (tau.1.verts.toFinset ∩ upsilon.1.verts.toFinset).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hinter
      simpa using hinter
    obtain ⟨x, hx⟩ := hcommon
    have hxparts := Finset.mem_inter.mp hx
    have hxtau : x ∈ tau.1.verts := List.mem_toFinset.mp hxparts.1
    have hxupsilon : x ∈ upsilon.1.verts := List.mem_toFinset.mp hxparts.2
    have hcontact :
        Relation.ReflTransGen (VertexLinkAdjacent K v) tau.1 upsilon.1 :=
      hlocal.vertexLinkPath_of_commonVertex tau.2 upsilon.2 hxtau hxupsilon
    exact hupsilonNot (Relation.ReflTransGen.trans htauReach hcontact)
  have hone :=
    (isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected)
      A B hAclosed hBclosed hcover (by simpa [hdisj])
  rcases hone with hsubA | hsubB
  · have hpB : triangulationTopologicalGeometricVertex rho.v0 ∈ B := by
      apply Set.mem_iUnion_of_mem ⟨rho, hrho⟩
      apply Set.mem_iUnion_of_mem hnpath
      apply subset_convexHull
      exact ⟨rho.v0, by simp [LinkTriangle.verts], rfl⟩
    have hplink : triangulationTopologicalGeometricVertex rho.v0 ∈
        triangulationTopologicalVertexLink K v := by
      apply (mem_triangulationTopologicalVertexLink_iff K v _).2
      refine ⟨rho, hrho, ?_⟩
      apply subset_convexHull
      exact ⟨rho.v0, by simp [LinkTriangle.verts], rfl⟩
    have hpA := hsubA hplink
    have : triangulationTopologicalGeometricVertex rho.v0 ∈ A ∩ B := ⟨hpA, hpB⟩
    rw [hdisj] at this
    exact this
  · have hpA : triangulationTopologicalGeometricVertex sigma.v0 ∈ A := by
      apply Set.mem_iUnion_of_mem ⟨sigma, hsigma⟩
      apply Set.mem_iUnion_of_mem Relation.ReflTransGen.refl
      apply subset_convexHull
      exact ⟨sigma.v0, by simp [LinkTriangle.verts], rfl⟩
    have hplink : triangulationTopologicalGeometricVertex sigma.v0 ∈
        triangulationTopologicalVertexLink K v := by
      apply (mem_triangulationTopologicalVertexLink_iff K v _).2
      refine ⟨sigma, hsigma, ?_⟩
      apply subset_convexHull
      exact ⟨sigma.v0, by simp [LinkTriangle.verts], rfl⟩
    have hpB := hsubB hplink
    have : triangulationTopologicalGeometricVertex sigma.v0 ∈ A ∩ B := ⟨hpA, hpB⟩
    rw [hdisj] at this
    exact this

end Poincare
