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

end Poincare
