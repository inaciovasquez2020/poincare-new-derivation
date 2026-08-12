import Poincare.DegreeFourConnectedLinkClassification
import Poincare.FiveTetGlobalClassification

namespace Poincare

/--
A nonempty target-present five-tetrahedron cluster that is closed under every
represented vertex star is global in a connected represented tetrahedron
overlap graph.

This is the non-circular global-saturation bridge needed by the degree-four
target-present branch.  No `PhiSupport = 0` hypothesis occurs here.
-/
theorem
    Move41Site.targetPresent_fiveTetCluster_global_of_vertexStarClosed
    {K : Triangulation}
    (hconn : TetrahedronVertexOverlapConnected K)
    (s : Move41Site)
    (C : Tet → Prop)
    (hseed :
      ∃ τ ∈ K.tets,
        C τ)
    (hstar :
      ∀ v : Nat,
        ∀ τ ∈ K.tets,
          C τ →
          v ∈ τ.verts →
          ∀ ρ ∈ K.tets,
            v ∈ ρ.verts →
            C ρ) :
    ∀ ρ ∈ K.tets,
      C ρ := by

  obtain ⟨τ₀, hτ₀K, hC₀⟩ := hseed

  have hstar' :
      ∀ τ ∈ K.tets,
        C τ →
        ∀ v ∈ τ.verts,
          ∀ ρ ∈ K.tets,
            v ∈ ρ.verts →
            C ρ := by

    intro τ hτK hCτ v hvτ ρ hρK hvρ

    exact
      hstar v τ hτK hCτ hvτ ρ hρK hvρ

  have hoverlap :
      ∀ τ ρ : Tet,
        τ ∈ K.tets →
        ρ ∈ K.tets →
        (τ.verts.toFinset ∩ ρ.verts.toFinset).Nonempty →
        C τ →
        C ρ :=
    tetrahedronCluster_overlap_closed_of_vertexStar_closed
      C
      hstar'

  exact
    hconn.all_of_overlap_closed
      C
      hτ₀K
      hC₀
      hoverlap


private theorem
    sharesEdge_exists_linkEdge_f0
    {σ ρ : LinkTriangle}
    (h : σ.SharesEdge ρ) :
    ∃ e : LinkEdge,
      e.InTriangle σ ∧
      e.InTriangle ρ := by

  unfold
    LinkTriangle.SharesEdge
    LinkTriangle.commonVertexCount at h

  let l :=
    σ.verts.eraseDups.filter
      (fun x => ρ.verts.contains x)

  have hl :
      2 ≤ l.length := h

  obtain ⟨a, b, t, heq⟩ :
      ∃ a b t,
        l = a :: b :: t := by

    cases hl0 : l with

    | nil =>
        simp [hl0] at hl

    | cons a l' =>

        cases hl1 : l' with

        | nil =>
            simp [hl0, hl1] at hl

        | cons b t =>
            exact
              ⟨a, b, t, by
                simp [hl0, hl1]⟩

  have hab :
      a ≠ b := by

    have hn :
        l.Nodup := by
      exact
        (eraseDups_nodup_nat σ.verts).filter
          (fun x => ρ.verts.contains x)

    rw [heq] at hn

    simp_all

  let e :=
    LinkEdge.ofDistinct a b hab

  have haL :
      a ∈ l := by
    rw [heq]
    simp

  have hbL :
      b ∈ l := by
    rw [heq]
    simp

  have haσ :
      a ∈ σ.verts := by

    have h := haL

    simp only [
      l,
      List.mem_filter,
      List.mem_eraseDups
    ] at h

    exact h.1

  have hbσ :
      b ∈ σ.verts := by

    have h := hbL

    simp only [
      l,
      List.mem_filter,
      List.mem_eraseDups
    ] at h

    exact h.1

  have haρ :
      a ∈ ρ.verts := by

    have h := haL

    simp only [
      l,
      List.mem_filter,
      List.mem_eraseDups
    ] at h

    simpa using h.2

  have hbρ :
      b ∈ ρ.verts := by

    have h := hbL

    simp only [
      l,
      List.mem_filter,
      List.mem_eraseDups
    ] at h

    simpa using h.2

  exact
    ⟨e,
      LinkEdge.ofDistinct_inTriangle
        σ a b hab haσ hbσ,
      LinkEdge.ofDistinct_inTriangle
        ρ a b hab haρ hbρ⟩


/--
If every supported vertex link is connected in the repository's
edge-adjacency sense, then any represented tetrahedron family that is closed
under represented common triangular faces is closed under the whole
represented vertex star of each of its tetrahedra.

This is the exact local propagation bridge needed by the target-present
five-tetrahedron branch.
-/
theorem
    ClosedTriangulationCore.tetrahedronCluster_vertexStar_closed_of_commonFace_closed
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (C : Tet → Prop)
    (hfaceClosed :
      ∀ α β : Tet,
        ∀ x y z : Nat,
          α ∈ K.tets →
          C α →
          β ∈ K.tets →
          [x, y, z].Nodup →
          (x ∈ α.verts ∧
            y ∈ α.verts ∧
            z ∈ α.verts) →
          (x ∈ β.verts ∧
            y ∈ β.verts ∧
            z ∈ β.verts) →
          C β) :
    ∀ α ∈ K.tets,
      C α →
      ∀ v ∈ α.verts,
        ∀ β ∈ K.tets,
          v ∈ β.verts →
          C β := by

  intro α hαK hCα
  intro v hvα
  intro β hβK hvβ

  have hvSupport :
      v ∈ vertexSupport K := by

    apply
      (mem_vertexSupport_iff K v).2

    simp only [
      allVerts,
      List.mem_flatMap
    ]

    exact
      ⟨α, hαK, hvα⟩

  have hconnected :
      VertexLinkConnected K v :=
    hlinks v hvSupport

  obtain
    ⟨σ₀, hσ₀, hαLink⟩ :=
      exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
        K v α hαK hvα

  obtain
    ⟨ψ, hψ, hβLink⟩ :=
      exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
        K v β hβK hvβ

  let D : LinkTriangle → Prop :=
    fun σ =>
      ∀ γ ∈ K.tets,
        γ.linkTriangleAt? v = some σ →
        C γ

  have hD₀ :
      D σ₀ := by

    intro γ hγK hγLink

    have hvγ :
        v ∈ γ.verts := by
      exact
        (γ.linkTriangleAt?_isSome_iff v).1
          (by
            rw [hγLink]
            rfl)

    have hvNotσ₀ :
        v ∉ σ₀.verts :=
      α.linkTriangleAt?_vertex_not_mem
        v σ₀
        (hcore.1 α hαK)
        hαLink

    have hv0 :
        v ≠ σ₀.v0 := by

      intro h

      apply hvNotσ₀

      simpa [
        LinkTriangle.verts,
        h
      ]

    have hv1 :
        v ≠ σ₀.v1 := by

      intro h

      apply hvNotσ₀

      simpa [
        LinkTriangle.verts,
        h
      ]

    have h01 :
        σ₀.v0 ≠ σ₀.v1 := by

      have hn :=
        vertexLinkTriangles_triangle_nodup
          K hcore v σ₀ hσ₀

      simp [
        LinkTriangle.verts
      ] at hn

      exact hn.1.1

    have hfaceNodup :
        [v, σ₀.v0, σ₀.v1].Nodup := by

      simp [
        hv0,
        hv1,
        h01
      ]

    have h0α :
        σ₀.v0 ∈ α.verts := by

      apply
        (α.mem_linkTriangleAt?_iff
          v σ₀.v0 σ₀
          hαLink
          (Ne.symm hv0)).1

      simp [
        LinkTriangle.verts
      ]

    have h1α :
        σ₀.v1 ∈ α.verts := by

      apply
        (α.mem_linkTriangleAt?_iff
          v σ₀.v1 σ₀
          hαLink
          (Ne.symm hv1)).1

      simp [
        LinkTriangle.verts
      ]

    have h0γ :
        σ₀.v0 ∈ γ.verts := by

      apply
        (γ.mem_linkTriangleAt?_iff
          v σ₀.v0 σ₀
          hγLink
          (Ne.symm hv0)).1

      simp [
        LinkTriangle.verts
      ]

    have h1γ :
        σ₀.v1 ∈ γ.verts := by

      apply
        (γ.mem_linkTriangleAt?_iff
          v σ₀.v1 σ₀
          hγLink
          (Ne.symm hv1)).1

      simp [
        LinkTriangle.verts
      ]

    exact
      hfaceClosed
        α γ
        v σ₀.v0 σ₀.v1
        hαK
        hCα
        hγK
        hfaceNodup
        ⟨hvα, h0α, h1α⟩
        ⟨hvγ, h0γ, h1γ⟩

  have hDclosed :
      ∀ σ ρ,
        VertexLinkAdjacent K v σ ρ →
        D σ →
        D ρ := by

    intro σ ρ hadj hDσ
    intro γ hγK hγLink

    obtain
      ⟨δ, hδK, hδLink⟩ :=
        (mem_vertexLinkTriangles_iff
          K v σ).1
          hadj.1

    have hCδ :
        C δ :=
      hDσ δ hδK hδLink

    obtain
      ⟨e, heσ, heρ⟩ :=
        hadj.2.2.elim
          sharesEdge_exists_linkEdge_f0
          (fun h => by
            obtain
              ⟨e, heρ, heσ⟩ :=
                sharesEdge_exists_linkEdge_f0 h

            exact
              ⟨e, heσ, heρ⟩)

    have hvδ :
        v ∈ δ.verts := by
      exact
        (δ.linkTriangleAt?_isSome_iff v).1
          (by
            rw [hδLink]
            rfl)

    have hvγ :
        v ∈ γ.verts := by
      exact
        (γ.linkTriangleAt?_isSome_iff v).1
          (by
            rw [hγLink]
            rfl)

    have hvNotσ :
        v ∉ σ.verts :=
      δ.linkTriangleAt?_vertex_not_mem
        v σ
        (hcore.1 δ hδK)
        hδLink

    have hvlo :
        v ≠ e.lo := by

      intro h

      apply hvNotσ

      simpa [h] using heσ.1

    have hvhi :
        v ≠ e.hi := by

      intro h

      apply hvNotσ

      simpa [h] using heσ.2

    have hlohi :
        e.lo ≠ e.hi :=
      e.sorted.ne

    have hfaceNodup :
        [v, e.lo, e.hi].Nodup := by

      simp [
        hvlo,
        hvhi,
        hlohi
      ]

    have hloδ :
        e.lo ∈ δ.verts := by

      exact
        (δ.mem_linkTriangleAt?_iff
          v e.lo σ
          hδLink
          (Ne.symm hvlo)).1
          heσ.1

    have hhiδ :
        e.hi ∈ δ.verts := by

      exact
        (δ.mem_linkTriangleAt?_iff
          v e.hi σ
          hδLink
          (Ne.symm hvhi)).1
          heσ.2

    have hloγ :
        e.lo ∈ γ.verts := by

      exact
        (γ.mem_linkTriangleAt?_iff
          v e.lo ρ
          hγLink
          (Ne.symm hvlo)).1
          heρ.1

    have hhiγ :
        e.hi ∈ γ.verts := by

      exact
        (γ.mem_linkTriangleAt?_iff
          v e.hi ρ
          hγLink
          (Ne.symm hvhi)).1
          heρ.2

    exact
      hfaceClosed
        δ γ
        v e.lo e.hi
        hδK
        hCδ
        hγK
        hfaceNodup
        ⟨hvδ, hloδ, hhiδ⟩
        ⟨hvγ, hloγ, hhiγ⟩

  have hDall :
      ∀ ρ ∈ vertexLinkTriangles K v,
        D ρ :=
    hconnected.all_of_adjacent_closed
      D
      hσ₀
      hD₀
      hDclosed

  exact
    hDall ψ hψ β hβK hβLink


/--
The concrete represented target-present five-tetrahedron cluster is closed
under every represented vertex star as soon as all supported vertex links are
connected.

This theorem uses the certified 20-face common-face closure and does not
assume `PhiSupport K = 0`.
-/
theorem
    Move41Site.represented_fiveTetCluster_vertexStarClosed_of_connectedLinks
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (s : Move41Site)
    {τ₀ τ₁ τ₂ τ₃ target : Tet}
    (hτ₀K : τ₀ ∈ K.tets)
    (hτ₀ :
      SameTetVertices τ₀ s.sourceTet₀)
    (hτ₁K : τ₁ ∈ K.tets)
    (hτ₁ :
      SameTetVertices τ₁ s.sourceTet₁)
    (hτ₂K : τ₂ ∈ K.tets)
    (hτ₂ :
      SameTetVertices τ₂ s.sourceTet₂)
    (hτ₃K : τ₃ ∈ K.tets)
    (hτ₃ :
      SameTetVertices τ₃ s.sourceTet₃)
    (htargetK :
      target ∈ K.tets)
    (htarget :
      SameTetVertices target s.targetTet)
    (hnodup :
      [τ₀, τ₁, τ₂, τ₃, target].Nodup) :
    ∀ α ∈ K.tets,
      (α = τ₀ ∨
        α = τ₁ ∨
        α = τ₂ ∨
        α = τ₃ ∨
        α = target) →
      ∀ v ∈ α.verts,
        ∀ β ∈ K.tets,
          v ∈ β.verts →
          (β = τ₀ ∨
            β = τ₁ ∨
            β = τ₂ ∨
            β = τ₃ ∨
            β = target) := by

  let C : Tet → Prop :=
    fun α =>
      α = τ₀ ∨
      α = τ₁ ∨
      α = τ₂ ∨
      α = τ₃ ∨
      α = target

  have hfaceClosed :
      ∀ α β : Tet,
        ∀ x y z : Nat,
          α ∈ K.tets →
          C α →
          β ∈ K.tets →
          [x, y, z].Nodup →
          (x ∈ α.verts ∧
            y ∈ α.verts ∧
            z ∈ α.verts) →
          (x ∈ β.verts ∧
            y ∈ β.verts ∧
            z ∈ β.verts) →
          C β := by

    intro α β x y z
    intro _hαK hCα hβK
    intro hxyz hαface hβface

    exact
      Move41Site.represented_fiveTetCluster_closed_under_common_face
        hcore
        s
        hτ₀K
        hτ₀
        hτ₁K
        hτ₁
        hτ₂K
        hτ₂
        hτ₃K
        hτ₃
        htargetK
        htarget
        hnodup
        α β
        x y z
        hCα
        hβK
        hxyz
        hαface
        hβface

  have hstar :=
    hcore.tetrahedronCluster_vertexStar_closed_of_commonFace_closed
      hlinks
      C
      hfaceClosed

  simpa [C] using hstar

end Poincare
