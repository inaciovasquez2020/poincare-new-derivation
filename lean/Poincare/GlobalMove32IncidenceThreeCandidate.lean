import Poincare.GlobalEdgeIncidenceThreeStarAdjacency
import Mathlib.Tactic

namespace Poincare

private theorem
    linkTriangle_support_of_three_distinct_mem
    (σ : LinkTriangle)
    (x a b : Nat)
    (hnodup : σ.verts.Nodup)
    (hx : x ∈ σ.verts)
    (ha : a ∈ σ.verts)
    (hb : b ∈ σ.verts)
    (hxa : x ≠ a)
    (hxb : x ≠ b)
    (hab : a ≠ b) :
    ∀ q : Nat,
      q ∈ σ.verts ↔
        q = x ∨ q = a ∨ q = b := by

  let S : Finset Nat := σ.verts.toFinset
  let T : Finset Nat := {x, a, b}

  have hTsub :
      T ⊆ S := by
    intro q hq

    have hcases :
        q = x ∨ q = a ∨ q = b := by
      simpa [T] using hq

    rcases hcases with rfl | rfl | rfl

    · exact List.mem_toFinset.mpr hx
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb

  have hScard :
      S.card = 3 := by
    change σ.verts.toFinset.card = 3
    rw [List.toFinset_card_of_nodup hnodup]
    simp [LinkTriangle.verts]

  have hTcard :
      T.card = 3 := by
    simp [
      T,
      hxa,
      hxb,
      hab,
      Ne.symm hxa,
      Ne.symm hxb,
      Ne.symm hab
    ]

  have hEq :
      T = S :=
    Finset.eq_of_subset_of_card_le
      hTsub
      (by omega)

  intro q

  have hmem :=
    congrArg
      (fun U : Finset Nat => q ∈ U)
      hEq.symm

  simpa [S, T] using hmem

private theorem
    no_three_distinct_linkTriangles_contain_same_linkEdge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x y : Nat)
    (σ₀ σ₁ σ₂ : LinkTriangle)
    (h01 : σ₀ ≠ σ₁)
    (h02 : σ₀ ≠ σ₂)
    (h12 : σ₁ ≠ σ₂)
    (hσ₀ : σ₀ ∈ vertexLinkTriangles K v)
    (hσ₁ : σ₁ ∈ vertexLinkTriangles K v)
    (hσ₂ : σ₂ ∈ vertexLinkTriangles K v)
    (hx₀ : x ∈ σ₀.verts)
    (hx₁ : x ∈ σ₁.verts)
    (hx₂ : x ∈ σ₂.verts)
    (hy₀ : y ∈ σ₀.verts)
    (hy₁ : y ∈ σ₁.verts)
    (hy₂ : y ∈ σ₂.verts)
    (hyx : y ≠ x) :
    False := by

  let eY :=
    LinkEdge.ofDistinct
      x y hyx.symm

  have he₀ :
      eY.InTriangle σ₀ :=
    LinkEdge.ofDistinct_inTriangle
      σ₀ x y hyx.symm hx₀ hy₀

  have he₁ :
      eY.InTriangle σ₁ :=
    LinkEdge.ofDistinct_inTriangle
      σ₁ x y hyx.symm hx₁ hy₁

  have he₂ :
      eY.InTriangle σ₂ :=
    LinkEdge.ofDistinct_inTriangle
      σ₂ x y hyx.symm hx₂ hy₂

  have hrep :
      eY.RepresentedAt K v :=
    ⟨σ₀, hσ₀, he₀⟩

  let L :=
    (vertexLinkTriangles K v).filter
      (fun σ =>
        decide (eY.InTriangle σ))

  have hlen :
      L.length = 2 := by
    dsimp [L]

    exact
      represented_linkEdge_link_incidence_two
        K hcore v eY hrep

  have hnodupL :
      L.Nodup := by
    dsimp [L]

    apply List.Nodup.filter

    exact
      vertexLinkTriangles_nodup
        K hcore v

  have hm₀ :
      σ₀ ∈ L := by
    simp [L, hσ₀, he₀]

  have hm₁ :
      σ₁ ∈ L := by
    simp [L, hσ₁, he₁]

  have hm₂ :
      σ₂ ∈ L := by
    simp [L, hσ₂, he₂]

  let A : Finset LinkTriangle :=
    {σ₀, σ₁, σ₂}

  have hAsub :
      A ⊆ L.toFinset := by
    intro σ hσ

    have hcases :
        σ = σ₀ ∨
        σ = σ₁ ∨
        σ = σ₂ := by
      simpa [A] using hσ

    rcases hcases with rfl | rfl | rfl

    · exact List.mem_toFinset.mpr hm₀
    · exact List.mem_toFinset.mpr hm₁
    · exact List.mem_toFinset.mpr hm₂

  have hAcard :
      A.card = 3 := by
    simp [
      A,
      h01,
      h02,
      h12,
      Ne.symm h01,
      Ne.symm h02,
      Ne.symm h12
    ]

  have hLcard :
      L.toFinset.card = L.length :=
    List.toFinset_card_of_nodup
      hnodupL

  have hle :
      A.card ≤ L.toFinset.card :=
    Finset.card_le_card hAsub

  omega

/--
The exact incidence-three star has the combinatorial support normal form

  {x,a,b}, {x,a,c}, {x,b,c}.

The represented-link-edge incidence-two theorem rules out coincidence
among the three outer adjacency witnesses.
-/
theorem
    ClosedTriangulationCore.exists_incidenceThree_vertexLink_support_normalForm
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hthree :
      (K.tets.filter
        (fun τ =>
          v ∈ τ.verts ∧
          x ∈ τ.verts)).length = 3) :
    ∃ σ₀ σ₁ σ₂ : LinkTriangle,
    ∃ a b c : Nat,
      σ₀ ∈ vertexLinkTriangles K v ∧
      σ₁ ∈ vertexLinkTriangles K v ∧
      σ₂ ∈ vertexLinkTriangles K v ∧
      a ≠ x ∧
      b ≠ x ∧
      c ≠ x ∧
      a ≠ b ∧
      a ≠ c ∧
      b ≠ c ∧
      (∀ q : Nat,
        q ∈ σ₀.verts ↔
          q = x ∨ q = a ∨ q = b) ∧
      (∀ q : Nat,
        q ∈ σ₁.verts ↔
          q = x ∨ q = a ∨ q = c) ∧
      (∀ q : Nat,
        q ∈ σ₂.verts ↔
          q = x ∨ q = b ∨ q = c) := by

  obtain
    ⟨σ₀, σ₁, σ₂,
      h01,
      h02,
      h12,
      hadj01,
      hadj02,
      hadj12⟩ :=
    hcore.exists_three_pairwiseAdjacent_vertexLinkStarTriangles_of_edgeIncidence_three
      v x hvx hthree

  have hs₀ :=
    (mem_vertexLinkStarTriangles_iff
      K v x σ₀).1 hadj01.1

  have hs₁ :=
    (mem_vertexLinkStarTriangles_iff
      K v x σ₁).1 hadj01.2.1

  have hs₂ :=
    (mem_vertexLinkStarTriangles_iff
      K v x σ₂).1 hadj02.2.1

  obtain
    ⟨a, hax, ha₀, ha₁⟩ :=
    hadj01.2.2

  obtain
    ⟨b, hbx, hb₀, hb₂⟩ :=
    hadj02.2.2

  obtain
    ⟨c, hcx, hc₁, hc₂⟩ :=
    hadj12.2.2

  have hab :
      a ≠ b := by
    intro hab
    subst b

    exact
      no_three_distinct_linkTriangles_contain_same_linkEdge
        hcore v x a
        σ₀ σ₁ σ₂
        h01 h02 h12
        hs₀.1 hs₁.1 hs₂.1
        hs₀.2 hs₁.2 hs₂.2
        ha₀ ha₁ hb₂
        hax

  have hac :
      a ≠ c := by
    intro hac
    subst c

    exact
      no_three_distinct_linkTriangles_contain_same_linkEdge
        hcore v x a
        σ₀ σ₁ σ₂
        h01 h02 h12
        hs₀.1 hs₁.1 hs₂.1
        hs₀.2 hs₁.2 hs₂.2
        ha₀ ha₁ hc₂
        hax

  have hbc :
      b ≠ c := by
    intro hbc
    subst c

    exact
      no_three_distinct_linkTriangles_contain_same_linkEdge
        hcore v x b
        σ₀ σ₁ σ₂
        h01 h02 h12
        hs₀.1 hs₁.1 hs₂.1
        hs₀.2 hs₁.2 hs₂.2
        hb₀ hc₁ hb₂
        hbx

  have hn₀ :=
    vertexLinkTriangles_triangle_nodup
      K hcore v σ₀ hs₀.1

  have hn₁ :=
    vertexLinkTriangles_triangle_nodup
      K hcore v σ₁ hs₁.1

  have hn₂ :=
    vertexLinkTriangles_triangle_nodup
      K hcore v σ₂ hs₂.1

  have hsup₀ :=
    linkTriangle_support_of_three_distinct_mem
      σ₀ x a b
      hn₀
      hs₀.2
      ha₀
      hb₀
      hax.symm
      hbx.symm
      hab

  have hsup₁ :=
    linkTriangle_support_of_three_distinct_mem
      σ₁ x a c
      hn₁
      hs₁.2
      ha₁
      hc₁
      hax.symm
      hcx.symm
      hac

  have hsup₂ :=
    linkTriangle_support_of_three_distinct_mem
      σ₂ x b c
      hn₂
      hs₂.2
      hb₂
      hc₂
      hbx.symm
      hcx.symm
      hbc

  exact
    ⟨σ₀, σ₁, σ₂,
      a, b, c,
      hs₀.1,
      hs₁.1,
      hs₂.1,
      hax,
      hbx,
      hcx,
      hab,
      hac,
      hbc,
      hsup₀,
      hsup₁,
      hsup₂⟩

private theorem
    sameTetVertices_of_linkTriangle_support
    (τ : Tet)
    (v x a b : Nat)
    (σ : LinkTriangle)
    (hExtract :
      τ.linkTriangleAt? v = some σ)
    (hsupport :
      ∀ q : Nat,
        q ∈ σ.verts ↔
          q = x ∨ q = a ∨ q = b) :
    SameTetVertices τ ⟨a, b, v, x⟩ := by

  intro q

  by_cases hqv :
      q = v

  · subst q

    have hvτ :
        v ∈ τ.verts := by
      rw [← τ.linkTriangleAt?_isSome_iff v]
      simp [hExtract]

    constructor

    · intro _
      simp [Tet.verts]

    · intro _
      exact hvτ

  · have hiff :
        q ∈ σ.verts ↔
          q ∈ τ.verts :=
      τ.mem_linkTriangleAt?_iff
        v q σ hExtract hqv

    rw [← hiff]
    rw [hsupport q]

    simp [
      Tet.verts,
      hqv,
      or_assoc,
      or_left_comm,
      or_comm
    ]

/--
Every closed-core ambient edge of tetrahedron-incidence exactly three
determines a realized Move32 candidate whose shared edge is that edge.
-/
theorem
    ClosedTriangulationCore.exists_move32Site_realizedIn_of_edgeIncidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (d e : Nat)
    (hde : d ≠ e)
    (hthree :
      (K.tets.filter
        (fun τ =>
          d ∈ τ.verts ∧
          e ∈ τ.verts)).length = 3) :
    ∃ s : Move32Site,
      s.d = d ∧
      s.e = e ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K := by

  obtain
    ⟨σ₀, σ₁, σ₂,
      a, b, c,
      hσ₀,
      hσ₁,
      hσ₂,
      _,
      _,
      _,
      _,
      _,
      _,
      hsup₀,
      hsup₁,
      hsup₂⟩ :=
    hcore.exists_incidenceThree_vertexLink_support_normalForm
      d e hde hthree

  obtain
    ⟨τ₀, hτ₀K, hExtract₀⟩ :=
    (mem_vertexLinkTriangles_iff
      K d σ₀).1 hσ₀

  obtain
    ⟨τ₁, hτ₁K, hExtract₁⟩ :=
    (mem_vertexLinkTriangles_iff
      K d σ₁).1 hσ₁

  obtain
    ⟨τ₂, hτ₂K, hExtract₂⟩ :=
    (mem_vertexLinkTriangles_iff
      K d σ₂).1 hσ₂

  have hsame₀ :
      SameTetVertices
        τ₀
        ⟨a, b, d, e⟩ :=
    sameTetVertices_of_linkTriangle_support
      τ₀ d e a b σ₀
      hExtract₀
      hsup₀

  have hsame₁ :
      SameTetVertices
        τ₁
        ⟨a, c, d, e⟩ :=
    sameTetVertices_of_linkTriangle_support
      τ₁ d e a c σ₁
      hExtract₁
      hsup₁

  have hsame₂ :
      SameTetVertices
        τ₂
        ⟨b, c, d, e⟩ :=
    sameTetVertices_of_linkTriangle_support
      τ₂ d e b c σ₂
      hExtract₂
      hsup₂

  let s : Move32Site :=
    ⟨a, b, c, d, e⟩

  refine
    ⟨s, rfl, rfl, ?_, ?_⟩

  · constructor

    · exact
        ⟨τ₀, hτ₀K,
          by
            simpa [
              s,
              Move32Site.targetTet₀
            ] using hsame₀⟩

    · constructor

      · exact
          ⟨τ₁, hτ₁K,
            by
              simpa [
                s,
                Move32Site.targetTet₁
              ] using hsame₁⟩

      · exact
          ⟨τ₂, hτ₂K,
            by
              simpa [
                s,
                Move32Site.targetTet₂
              ] using hsame₂⟩

  · simpa [
      s,
      Move32Site.SharedEdgeExactlyThree
    ] using hthree

end Poincare
