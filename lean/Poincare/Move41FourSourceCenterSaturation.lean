import Poincare.Move41FourSourceCenterFaceClosure

namespace Poincare

private theorem nodup_eraseDups_nat_for_sourceCluster (l : List Nat) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons a l =>
      rw [List.eraseDups_cons]
      constructor
      · intro x hx hax
        have hx' := List.mem_eraseDups.1 hx
        simp [hax] at hx'
      · exact nodup_eraseDups_nat_for_sourceCluster _
termination_by l.length
decreasing_by
  exact lt_of_le_of_lt (List.length_filter_le _ _) (Nat.lt_succ_self _)

private theorem sharesEdge_exists_linkEdge_for_sourceCluster
    {σ ρ : LinkTriangle} (h : σ.SharesEdge ρ) :
    ∃ e : LinkEdge, e.InTriangle σ ∧ e.InTriangle ρ := by
  unfold LinkTriangle.SharesEdge LinkTriangle.commonVertexCount at h
  let l := σ.verts.eraseDups.filter (fun x => ρ.verts.contains x)
  have hl : 2 ≤ l.length := h
  obtain ⟨a, b, t, heq⟩ : ∃ a b t, l = a :: b :: t := by
    cases hlst : l with
    | nil => simp [hlst] at hl
    | cons a l =>
      cases hlst2 : l with
      | nil => simp [hlst, hlst2] at hl
      | cons b t => exact ⟨a, b, t, rfl⟩
  have hab : a ≠ b := by
    have hn : l.Nodup := (nodup_eraseDups_nat_for_sourceCluster σ.verts).filter _
    rw [heq] at hn
    simp_all
  let e := LinkEdge.ofDistinct a b hab
  refine ⟨e, LinkEdge.ofDistinct_inTriangle σ a b hab ?_ ?_,
    LinkEdge.ofDistinct_inTriangle ρ a b hab ?_ ?_⟩
  · have hm : a ∈ l := by rw [heq]; simp
    exact List.mem_eraseDups.1 (List.mem_filter.1 hm).1
  · have hm : b ∈ l := by rw [heq]; simp
    exact List.mem_eraseDups.1 (List.mem_filter.1 hm).1
  · have hm : a ∈ l := by rw [heq]; simp
    simpa using (List.mem_filter.1 hm).2
  · have hm : b ∈ l := by rw [heq]; simp
    simpa using (List.mem_filter.1 hm).2

/--
If the four represented source tetrahedra of a Move41 site are already
closed under every center-containing triangular face, connectedness of the
center vertex link forces them to exhaust the entire represented center star.

This is the missing local-star saturation input for the target-free
four-source center-degree theorem.
-/
theorem Move41Site.represented_sourceCluster_saturates_center_of_connectedLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site)
    {tau₀ tau₁ tau₂ tau₃ : Tet}
    (htau₀K : tau₀ ∈ K.tets)
    (htau₀ : SameTetVertices tau₀ s.sourceTet₀)
    (htau₁K : tau₁ ∈ K.tets)
    (htau₁ : SameTetVertices tau₁ s.sourceTet₁)
    (htau₂K : tau₂ ∈ K.tets)
    (htau₂ : SameTetVertices tau₂ s.sourceTet₂)
    (htau₃K : tau₃ ∈ K.tets)
    (htau₃ : SameTetVertices tau₃ s.sourceTet₃)
    (hnodup : [tau₀, tau₁, tau₂, tau₃].Nodup)
    (hconnected : VertexLinkConnected K s.e) :
    ∀ tau ∈ K.tets,
      s.e ∈ tau.verts →
      ∃ source ∈ s.sourceTets,
        SameTetVertices tau source := by
  classical

  let cluster : List Tet :=
    [tau₀, tau₁, tau₂, tau₃]

  let C : LinkTriangle → Prop :=
    fun σ =>
      ∃ alpha,
        alpha ∈ K.tets ∧
        alpha.linkTriangleAt? s.e = some σ ∧
        (alpha = tau₀ ∨
          alpha = tau₁ ∨
          alpha = tau₂ ∨
          alpha = tau₃)

  have he₀ : s.e ∈ tau₀.verts := by
    apply (htau₀ s.e).2
    simp [
      Move41Site.sourceTet₀,
      Tet.verts
    ]

  obtain ⟨σ₀, hσ₀, hExtract₀⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
      K s.e tau₀ htau₀K he₀

  have hC₀ : C σ₀ := by
    exact
      ⟨tau₀, htau₀K, hExtract₀,
        Or.inl rfl⟩

  have hclosed :
      ∀ σ ρ,
        VertexLinkAdjacent K s.e σ ρ →
        C σ →
        C ρ := by
    intro σ ρ hadj hCσ

    obtain
      ⟨alpha, halphaK,
        halphaExtract, halphaCluster⟩ :=
      hCσ

    obtain ⟨beta, hbetaK, hbetaExtract⟩ :=
      (mem_vertexLinkTriangles_iff K s.e ρ).1
        hadj.2.1

    obtain ⟨edge, hedgeσ, hedgeρ⟩ :
        ∃ edge : LinkEdge,
          edge.InTriangle σ ∧
          edge.InTriangle ρ := by
      rcases hadj.2.2 with hshare | hshare

      · exact
          sharesEdge_exists_linkEdge_for_sourceCluster
            hshare

      · obtain ⟨edge, hedgeρ, hedgeσ⟩ :=
          sharesEdge_exists_linkEdge_for_sourceCluster
            hshare

        exact
          ⟨edge, hedgeσ, hedgeρ⟩

    have halphaNodup :
        alpha.verts.Nodup :=
      hcore.1 alpha halphaK

    have hcenterNot :
        s.e ∉ σ.verts :=
      alpha.linkTriangleAt?_vertex_not_mem
        s.e σ halphaNodup halphaExtract

    have hlo :
        edge.lo ≠ s.e := by
      intro h
      apply hcenterNot
      rw [← h]
      exact hedgeσ.1

    have hhi :
        edge.hi ≠ s.e := by
      intro h
      apply hcenterNot
      rw [← h]
      exact hedgeσ.2

    have hcenterLo :
        s.e ≠ edge.lo :=
      Ne.symm hlo

    have hcenterHi :
        s.e ≠ edge.hi :=
      Ne.symm hhi

    have hloHi :
        edge.lo ≠ edge.hi :=
      Nat.ne_of_lt edge.sorted

    have hfaceNodup :
        [s.e, edge.lo, edge.hi].Nodup := by
      simp [
        hcenterLo,
        hcenterHi,
        hloHi
      ]

    have halphaFace :
        s.e ∈ alpha.verts ∧
        edge.lo ∈ alpha.verts ∧
        edge.hi ∈ alpha.verts :=
      (alpha.linkTriangleAt?_edge_iff
        s.e σ edge
        halphaExtract hlo hhi).1
        hedgeσ

    have hbetaFace :
        s.e ∈ beta.verts ∧
        edge.lo ∈ beta.verts ∧
        edge.hi ∈ beta.verts :=
      (beta.linkTriangleAt?_edge_iff
        s.e ρ edge
        hbetaExtract hlo hhi).1
        hedgeρ

    have hbetaCluster :
        beta = tau₀ ∨
        beta = tau₁ ∨
        beta = tau₂ ∨
        beta = tau₃ :=
      Move41Site.represented_sourceCluster_closed_under_center_face
        hcore
        s
        htau₀K htau₀
        htau₁K htau₁
        htau₂K htau₂
        htau₃K htau₃
        hnodup
        alpha beta
        edge.lo edge.hi
        halphaCluster
        hbetaK
        hfaceNodup
        halphaFace
        hbetaFace

    exact
      ⟨beta, hbetaK,
        hbetaExtract,
        hbetaCluster⟩

  have hall :
      ∀ ρ ∈ vertexLinkTriangles K s.e,
        C ρ :=
    hconnected.all_of_adjacent_closed
      C
      hσ₀
      hC₀
      hclosed

  intro tau htauK heTau

  obtain ⟨σ, hσK, htauExtract⟩ :=
    exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
      K s.e tau htauK heTau

  obtain
    ⟨beta, hbetaK,
      hbetaExtract, hbetaCluster⟩ :=
    hall σ hσK

  have heBeta :
      s.e ∈ beta.verts := by
    apply
      (beta.linkTriangleAt?_isSome_iff
        s.e).1
    rw [hbetaExtract]
    rfl

  have hsame :
      SameTetVertices tau beta := by
    intro x

    by_cases hxe :
        x = s.e

    · subst x

      exact
        ⟨fun _ => heBeta,
          fun _ => heTau⟩

    · constructor

      · intro hxTau

        have hxSigma :
            x ∈ σ.verts :=
          (tau.mem_linkTriangleAt?_iff
            s.e x σ
            htauExtract hxe).2
            hxTau

        exact
          (beta.mem_linkTriangleAt?_iff
            s.e x σ
            hbetaExtract hxe).1
            hxSigma

      · intro hxBeta

        have hxSigma :
            x ∈ σ.verts :=
          (beta.mem_linkTriangleAt?_iff
            s.e x σ
            hbetaExtract hxe).2
            hxBeta

        exact
          (tau.mem_linkTriangleAt?_iff
            s.e x σ
            htauExtract hxe).1
            hxSigma

  rcases hbetaCluster with
    rfl | rfl | rfl | rfl

  · refine
      ⟨s.sourceTet₀,
        ?_,
        sameTetVertices_trans
          hsame htau₀⟩

    simp [Move41Site.sourceTets]

  · refine
      ⟨s.sourceTet₁,
        ?_,
        sameTetVertices_trans
          hsame htau₁⟩

    simp [Move41Site.sourceTets]

  · refine
      ⟨s.sourceTet₂,
        ?_,
        sameTetVertices_trans
          hsame htau₂⟩

    simp [Move41Site.sourceTets]

  · refine
      ⟨s.sourceTet₃,
        ?_,
        sameTetVertices_trans
          hsame htau₃⟩

    simp [Move41Site.sourceTets]

end Poincare
