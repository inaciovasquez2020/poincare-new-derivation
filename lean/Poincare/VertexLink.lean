import Poincare.Validity
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Poincare

structure LinkTriangle where
  v0 : Nat
  v1 : Nat
  v2 : Nat
deriving DecidableEq

def LinkTriangle.verts (σ : LinkTriangle) : List Nat :=
  [σ.v0, σ.v1, σ.v2]

def Tet.linkTriangleAt? (τ : Tet) (v : Nat) : Option LinkTriangle :=
  if v = τ.v0 then
    some ⟨τ.v1, τ.v2, τ.v3⟩
  else if v = τ.v1 then
    some ⟨τ.v0, τ.v2, τ.v3⟩
  else if v = τ.v2 then
    some ⟨τ.v0, τ.v1, τ.v3⟩
  else if v = τ.v3 then
    some ⟨τ.v0, τ.v1, τ.v2⟩
  else
    none

def vertexLinkTriangles
    (K : Triangulation) (v : Nat) : List LinkTriangle :=
  K.tets.filterMap
    (fun τ => τ.linkTriangleAt? v)

theorem mem_vertexLinkTriangles_iff
    (K : Triangulation)
    (v : Nat)
    (σ : LinkTriangle) :
    σ ∈ vertexLinkTriangles K v ↔
      ∃ τ ∈ K.tets,
        τ.linkTriangleAt? v = some σ := by
  simp [vertexLinkTriangles]

theorem Tet.linkTriangleAt?_eq_none_iff
    (τ : Tet) (v : Nat) :
    τ.linkTriangleAt? v = none ↔
      v ∉ τ.verts := by

  by_cases h0 : v = τ.v0
  · subst v
    simp [
      Tet.linkTriangleAt?,
      Tet.verts
    ]

  by_cases h1 : v = τ.v1
  · subst v
    simp [
      Tet.linkTriangleAt?,
      Tet.verts,
      h0
    ]

  by_cases h2 : v = τ.v2
  · subst v
    simp [
      Tet.linkTriangleAt?,
      Tet.verts,
      h0,
      h1
    ]

  by_cases h3 : v = τ.v3
  · subst v
    simp [
      Tet.linkTriangleAt?,
      Tet.verts,
      h0,
      h1,
      h2
    ]

  · simp [
      Tet.linkTriangleAt?,
      Tet.verts,
      h0,
      h1,
      h2,
      h3
    ]

theorem Tet.linkTriangleAt?_isSome_iff
    (τ : Tet) (v : Nat) :
    (τ.linkTriangleAt? v).isSome = true ↔
      v ∈ τ.verts := by
  rw [← Option.ne_none_iff_isSome]
  rw [ne_eq, Tet.linkTriangleAt?_eq_none_iff]
  simp


theorem Tet.linkTriangleAt?_nodup
    (τ : Tet)
    (v : Nat)
    (σ : LinkTriangle)
    (hτ : τ.verts.Nodup)
    (hσ : τ.linkTriangleAt? v = some σ) :
    σ.verts.Nodup := by

  unfold Tet.linkTriangleAt? at hσ

  by_cases h0 : v = τ.v0
  · rw [if_pos h0] at hσ
    injection hσ with hs
    subst σ
    simp_all [
      Tet.verts,
      LinkTriangle.verts
    ]

  · rw [if_neg h0] at hσ

    by_cases h1 : v = τ.v1
    · rw [if_pos h1] at hσ
      injection hσ with hs
      subst σ
      simp_all [
        Tet.verts,
        LinkTriangle.verts
      ]

    · rw [if_neg h1] at hσ

      by_cases h2 : v = τ.v2
      · rw [if_pos h2] at hσ
        injection hσ with hs
        subst σ
        simp_all [
          Tet.verts,
          LinkTriangle.verts
        ]

      · rw [if_neg h2] at hσ

        by_cases h3 : v = τ.v3
        · rw [if_pos h3] at hσ
          injection hσ with hs
          subst σ
          simp_all [
            Tet.verts,
            LinkTriangle.verts
          ]

        · rw [if_neg h3] at hσ
          simp at hσ


theorem vertexLinkTriangles_triangle_nodup
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (σ : LinkTriangle)
    (hσ : σ ∈ vertexLinkTriangles K v) :
    σ.verts.Nodup := by

  rcases
      (mem_vertexLinkTriangles_iff K v σ).1 hσ with
    ⟨τ, hτK, hExtract⟩

  have hτNodup : τ.verts.Nodup :=
    hcore.1 τ hτK

  exact
    τ.linkTriangleAt?_nodup
      v σ hτNodup hExtract


structure LinkEdge where
  lo : Nat
  hi : Nat
  sorted : lo < hi

def LinkEdge.InTriangle
    (e : LinkEdge)
    (σ : LinkTriangle) : Prop :=
  e.lo ∈ σ.verts ∧
  e.hi ∈ σ.verts

def LinkEdge.RepresentedAt
    (e : LinkEdge)
    (K : Triangulation)
    (v : Nat) : Prop :=
  ∃ σ ∈ vertexLinkTriangles K v,
    e.InTriangle σ


theorem Tet.linkTriangleAt?_verts_subset
    (τ : Tet)
    (v : Nat)
    (σ : LinkTriangle)
    (hσ : τ.linkTriangleAt? v = some σ) :
    ∀ x ∈ σ.verts, x ∈ τ.verts := by

  unfold Tet.linkTriangleAt? at hσ

  by_cases h0 : v = τ.v0
  · rw [if_pos h0] at hσ
    injection hσ with hs
    subst σ
    intro x hx
    simp only [
      LinkTriangle.verts,
      Tet.verts,
      List.mem_cons,
      List.mem_singleton
    ] at hx ⊢
    aesop

  · rw [if_neg h0] at hσ

    by_cases h1 : v = τ.v1
    · rw [if_pos h1] at hσ
      injection hσ with hs
      subst σ
      intro x hx
      simp only [
        LinkTriangle.verts,
        Tet.verts,
        List.mem_cons,
        List.mem_singleton
      ] at hx ⊢
      aesop

    · rw [if_neg h1] at hσ

      by_cases h2 : v = τ.v2
      · rw [if_pos h2] at hσ
        injection hσ with hs
        subst σ
        intro x hx
        simp only [
          LinkTriangle.verts,
          Tet.verts,
          List.mem_cons,
          List.mem_singleton
        ] at hx ⊢
        aesop

      · rw [if_neg h2] at hσ

        by_cases h3 : v = τ.v3
        · rw [if_pos h3] at hσ
          injection hσ with hs
          subst σ
          intro x hx
          simp only [
            LinkTriangle.verts,
            Tet.verts,
            List.mem_cons,
            List.mem_singleton
          ] at hx ⊢
          aesop

        · rw [if_neg h3] at hσ
          simp at hσ


theorem Tet.linkTriangleAt?_vertex_not_mem
    (τ : Tet)
    (v : Nat)
    (σ : LinkTriangle)
    (hτ : τ.verts.Nodup)
    (hσ : τ.linkTriangleAt? v = some σ) :
    v ∉ σ.verts := by

  unfold Tet.linkTriangleAt? at hσ

  by_cases h0 : v = τ.v0
  · rw [if_pos h0] at hσ
    injection hσ with hs
    subst σ
    simp_all [
      Tet.verts,
      LinkTriangle.verts
    ]

  · rw [if_neg h0] at hσ

    by_cases h1 : v = τ.v1
    · rw [if_pos h1] at hσ
      injection hσ with hs
      subst σ
      simp_all [
        Tet.verts,
        LinkTriangle.verts
      ]

    · rw [if_neg h1] at hσ

      by_cases h2 : v = τ.v2
      · rw [if_pos h2] at hσ
        injection hσ with hs
        subst σ
        simp_all [
          Tet.verts,
          LinkTriangle.verts
        ]

      · rw [if_neg h2] at hσ

        by_cases h3 : v = τ.v3
        · rw [if_pos h3] at hσ
          injection hσ with hs
          subst σ
          simp_all [
            Tet.verts,
            LinkTriangle.verts
          ]

        · rw [if_neg h3] at hσ
          simp at hσ


theorem represented_linkEdge_ambient_incidence_two
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : LinkEdge)
    (hrep : e.RepresentedAt K v) :
    (K.tets.filter
      (fun τ =>
        v ∈ τ.verts ∧
        e.lo ∈ τ.verts ∧
        e.hi ∈ τ.verts)).length = 2 := by

  rcases hrep with
    ⟨σ, hσLink, hEdge⟩

  rcases
      (mem_vertexLinkTriangles_iff K v σ).1 hσLink with
    ⟨τ, hτK, hExtract⟩

  have hτNodup : τ.verts.Nodup :=
    hcore.1 τ hτK

  have hvSome :
      (τ.linkTriangleAt? v).isSome = true := by
    rw [hExtract]
    rfl

  have hvTet : v ∈ τ.verts :=
    (τ.linkTriangleAt?_isSome_iff v).1 hvSome

  have hsubset :
      ∀ x ∈ σ.verts, x ∈ τ.verts :=
    τ.linkTriangleAt?_verts_subset
      v σ hExtract

  have hloTet : e.lo ∈ τ.verts :=
    hsubset e.lo hEdge.1

  have hhiTet : e.hi ∈ τ.verts :=
    hsubset e.hi hEdge.2

  have hvNot :
      v ∉ σ.verts :=
    τ.linkTriangleAt?_vertex_not_mem
      v σ hτNodup hExtract

  have hvlo : v ≠ e.lo := by
    intro h
    apply hvNot
    rw [h]
    exact hEdge.1

  have hvhi : v ≠ e.hi := by
    intro h
    apply hvNot
    rw [h]
    exact hEdge.2

  have hlohi : e.lo ≠ e.hi :=
    Nat.ne_of_lt e.sorted

  have hfaceNodup :
      [v, e.lo, e.hi].Nodup := by
    simp [
      hvlo,
      hvhi,
      hlohi
    ]

  have hrepresented :
      ∃ ρ ∈ K.tets,
        v ∈ ρ.verts ∧
        e.lo ∈ ρ.verts ∧
        e.hi ∈ ρ.verts := by
    exact
      ⟨τ, hτK, hvTet, hloTet, hhiTet⟩

  exact
    hcore.2.2
      v e.lo e.hi
      hfaceNodup
      hrepresented


instance instDecidableLinkEdgeInTriangle
    (e : LinkEdge)
    (σ : LinkTriangle) :
    Decidable (e.InTriangle σ) := by
  unfold LinkEdge.InTriangle
  infer_instance


theorem Tet.mem_linkTriangleAt?_iff
    (τ : Tet)
    (v x : Nat)
    (σ : LinkTriangle)
    (hσ : τ.linkTriangleAt? v = some σ)
    (hxv : x ≠ v) :
    x ∈ σ.verts ↔ x ∈ τ.verts := by

  constructor

  · intro hx
    exact
      τ.linkTriangleAt?_verts_subset
        v σ hσ x hx

  · intro hxTet

    unfold Tet.linkTriangleAt? at hσ

    by_cases h0 : v = τ.v0
    · rw [if_pos h0] at hσ
      injection hσ with hs
      subst σ
      simp_all [
        Tet.verts,
        LinkTriangle.verts
      ]

    · rw [if_neg h0] at hσ

      by_cases h1 : v = τ.v1
      · rw [if_pos h1] at hσ
        injection hσ with hs
        subst σ
        simp_all [
          Tet.verts,
          LinkTriangle.verts
        ]

      · rw [if_neg h1] at hσ

        by_cases h2 : v = τ.v2
        · rw [if_pos h2] at hσ
          injection hσ with hs
          subst σ
          simp_all [
            Tet.verts,
            LinkTriangle.verts
          ]

        · rw [if_neg h2] at hσ

          by_cases h3 : v = τ.v3
          · rw [if_pos h3] at hσ
            injection hσ with hs
            subst σ
            simp_all [
              Tet.verts,
              LinkTriangle.verts
            ]

          · rw [if_neg h3] at hσ
            simp at hσ


theorem Tet.linkTriangleAt?_edge_iff
    (τ : Tet)
    (v : Nat)
    (σ : LinkTriangle)
    (e : LinkEdge)
    (hσ : τ.linkTriangleAt? v = some σ)
    (hlo : e.lo ≠ v)
    (hhi : e.hi ≠ v) :
    e.InTriangle σ ↔
      v ∈ τ.verts ∧
      e.lo ∈ τ.verts ∧
      e.hi ∈ τ.verts := by

  have hvSome :
      (τ.linkTriangleAt? v).isSome = true := by
    rw [hσ]
    rfl

  have hvTet : v ∈ τ.verts :=
    (τ.linkTriangleAt?_isSome_iff v).1 hvSome

  have hloIff :
      e.lo ∈ σ.verts ↔
        e.lo ∈ τ.verts :=
    τ.mem_linkTriangleAt?_iff
      v e.lo σ hσ hlo

  have hhiIff :
      e.hi ∈ σ.verts ↔
        e.hi ∈ τ.verts :=
    τ.mem_linkTriangleAt?_iff
      v e.hi σ hσ hhi

  constructor

  · intro hEdge
    exact
      ⟨hvTet,
       hloIff.1 hEdge.1,
       hhiIff.1 hEdge.2⟩

  · rintro ⟨_, hloTet, hhiTet⟩
    exact
      ⟨hloIff.2 hloTet,
       hhiIff.2 hhiTet⟩


theorem LinkEdge.RepresentedAt_center_ne
    (e : LinkEdge)
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hrep : e.RepresentedAt K v) :
    v ≠ e.lo ∧
    v ≠ e.hi := by

  rcases hrep with
    ⟨σ, hσLink, hEdge⟩

  rcases
      (mem_vertexLinkTriangles_iff K v σ).1 hσLink with
    ⟨τ, hτK, hExtract⟩

  have hτNodup : τ.verts.Nodup :=
    hcore.1 τ hτK

  have hvNot :
      v ∉ σ.verts :=
    τ.linkTriangleAt?_vertex_not_mem
      v σ hτNodup hExtract

  constructor

  · intro h
    apply hvNot
    rw [h]
    exact hEdge.1

  · intro h
    apply hvNot
    rw [h]
    exact hEdge.2


theorem linkEdge_filterMap_incidence_count_eq
    (tets : List Tet)
    (v : Nat)
    (e : LinkEdge)
    (hvlo : v ≠ e.lo)
    (hvhi : v ≠ e.hi) :
    ((tets.filterMap
        (fun τ => τ.linkTriangleAt? v)).filter
      (fun σ => decide (e.InTriangle σ))).length =
    (tets.filter
      (fun τ =>
        decide (
          v ∈ τ.verts ∧
          e.lo ∈ τ.verts ∧
          e.hi ∈ τ.verts))).length := by

  induction tets with

  | nil =>
      simp

  | cons τ rest ih =>

      cases hopt :
          τ.linkTriangleAt? v with

      | none =>

          have hvNot : v ∉ τ.verts :=
            (τ.linkTriangleAt?_eq_none_iff v).1 hopt

          simp [
            hopt,
            hvNot,
            ih
          ]

      | some σ =>

          have hEdgeIff :
              e.InTriangle σ ↔
                v ∈ τ.verts ∧
                e.lo ∈ τ.verts ∧
                e.hi ∈ τ.verts :=
            τ.linkTriangleAt?_edge_iff
              v σ e hopt
              (Ne.symm hvlo)
              (Ne.symm hvhi)

          by_cases hEdge :
              e.InTriangle σ

          · have hAmbient :
                v ∈ τ.verts ∧
                e.lo ∈ τ.verts ∧
                e.hi ∈ τ.verts :=
              hEdgeIff.1 hEdge

            simp [
              hopt,
              hEdge,
              hAmbient,
              ih
            ]

          · have hAmbient :
                ¬ (
                  v ∈ τ.verts ∧
                  e.lo ∈ τ.verts ∧
                  e.hi ∈ τ.verts
                ) := by
              intro h
              exact hEdge (hEdgeIff.2 h)

            simp [
              hopt,
              hEdge,
              hAmbient,
              ih
            ]


theorem vertexLinkTriangles_edge_incidence_count_eq
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : LinkEdge)
    (hrep : e.RepresentedAt K v) :
    ((vertexLinkTriangles K v).filter
      (fun σ => decide (e.InTriangle σ))).length =
    (K.tets.filter
      (fun τ =>
        decide (
          v ∈ τ.verts ∧
          e.lo ∈ τ.verts ∧
          e.hi ∈ τ.verts))).length := by

  have hne :
      v ≠ e.lo ∧
      v ≠ e.hi :=
    e.RepresentedAt_center_ne
      K hcore v hrep

  unfold vertexLinkTriangles

  exact
    linkEdge_filterMap_incidence_count_eq
      K.tets
      v e
      hne.1
      hne.2


theorem represented_linkEdge_link_incidence_two
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : LinkEdge)
    (hrep : e.RepresentedAt K v) :
    ((vertexLinkTriangles K v).filter
      (fun σ => decide (e.InTriangle σ))).length = 2 := by

  rw [
    vertexLinkTriangles_edge_incidence_count_eq
      K hcore v e hrep
  ]

  exact
    represented_linkEdge_ambient_incidence_two
      K hcore v e hrep


def LinkTriangle.commonVertexCount
    (σ ρ : LinkTriangle) : Nat :=
  (σ.verts.eraseDups.filter
    (fun x => ρ.verts.contains x)).length

def LinkTriangle.SharesEdge
    (σ ρ : LinkTriangle) : Prop :=
  2 ≤ σ.commonVertexCount ρ

instance instDecidableLinkTriangleSharesEdge
    (σ ρ : LinkTriangle) :
    Decidable (σ.SharesEdge ρ) := by
  unfold LinkTriangle.SharesEdge
  infer_instance


def VertexLinkAdjacent
    (K : Triangulation)
    (v : Nat)
    (σ ρ : LinkTriangle) : Prop :=
  σ ∈ vertexLinkTriangles K v ∧
  ρ ∈ vertexLinkTriangles K v ∧
  (
    σ.SharesEdge ρ ∨
    ρ.SharesEdge σ
  )


instance instDecidableVertexLinkAdjacent
    (K : Triangulation)
    (v : Nat)
    (σ ρ : LinkTriangle) :
    Decidable (VertexLinkAdjacent K v σ ρ) := by
  unfold VertexLinkAdjacent
  infer_instance


theorem VertexLinkAdjacent.symm
    (K : Triangulation)
    (v : Nat)
    (σ ρ : LinkTriangle) :
    VertexLinkAdjacent K v σ ρ →
      VertexLinkAdjacent K v ρ σ := by
  rintro ⟨hσ, hρ, hshare⟩
  refine ⟨hρ, hσ, ?_⟩
  rcases hshare with h | h
  · exact Or.inr h
  · exact Or.inl h


def VertexLinkConnected
    (K : Triangulation)
    (v : Nat) : Prop :=
  ∀ σ ∈ vertexLinkTriangles K v,
    ∀ ρ ∈ vertexLinkTriangles K v,
      Relation.ReflTransGen
        (VertexLinkAdjacent K v)
        σ ρ


def ConnectedLinkClosedCore
    (K : Triangulation) : Prop :=
  ClosedTriangulationCore K ∧
  ∀ v ∈ vertexSupport K,
    VertexLinkConnected K v


theorem ConnectedLinkClosedCore.closedCore
    (K : Triangulation)
    (h : ConnectedLinkClosedCore K) :
    ClosedTriangulationCore K :=
  h.1


theorem ConnectedLinkClosedCore.vertexLinkConnected
    (K : Triangulation)
    (h : ConnectedLinkClosedCore K)
    (v : Nat)
    (hv : v ∈ vertexSupport K) :
    VertexLinkConnected K v :=
  h.2 v hv



def vertexLinkStarTriangles
    (K : Triangulation)
    (v x : Nat) : List LinkTriangle :=
  (vertexLinkTriangles K v).filter
    (fun σ => decide (x ∈ σ.verts))


theorem mem_vertexLinkStarTriangles_iff
    (K : Triangulation)
    (v x : Nat)
    (σ : LinkTriangle) :
    σ ∈ vertexLinkStarTriangles K v x ↔
      σ ∈ vertexLinkTriangles K v ∧
      x ∈ σ.verts := by
  simp [
    vertexLinkStarTriangles
  ]


def VertexLinkVertexRepresented
    (K : Triangulation)
    (v x : Nat) : Prop :=
  ∃ σ ∈ vertexLinkTriangles K v,
    x ∈ σ.verts


theorem vertexLinkVertexRepresented_iff_star_nonempty
    (K : Triangulation)
    (v x : Nat) :
    VertexLinkVertexRepresented K v x ↔
      ∃ σ,
        σ ∈ vertexLinkStarTriangles K v x := by

  constructor

  · rintro ⟨σ, hσ, hx⟩
    exact
      ⟨σ,
       (mem_vertexLinkStarTriangles_iff
          K v x σ).2
          ⟨hσ, hx⟩⟩

  · rintro ⟨σ, hσ⟩
    have h :=
      (mem_vertexLinkStarTriangles_iff
        K v x σ).1 hσ
    exact
      ⟨σ, h.1, h.2⟩


def VertexLinkStarAdjacent
    (K : Triangulation)
    (v x : Nat)
    (σ ρ : LinkTriangle) : Prop :=
  σ ∈ vertexLinkStarTriangles K v x ∧
  ρ ∈ vertexLinkStarTriangles K v x ∧
  ∃ y : Nat,
    y ≠ x ∧
    y ∈ σ.verts ∧
    y ∈ ρ.verts


theorem VertexLinkStarAdjacent.symm
    (K : Triangulation)
    (v x : Nat)
    (σ ρ : LinkTriangle) :
    VertexLinkStarAdjacent K v x σ ρ →
      VertexLinkStarAdjacent K v x ρ σ := by

  rintro
    ⟨hσ, hρ, y, hyx, hyσ, hyρ⟩

  exact
    ⟨hρ, hσ, y, hyx, hyρ, hyσ⟩


theorem VertexLinkStarAdjacent.left_mem
    (K : Triangulation)
    (v x : Nat)
    (σ ρ : LinkTriangle)
    (h :
      VertexLinkStarAdjacent K v x σ ρ) :
    σ ∈ vertexLinkStarTriangles K v x :=
  h.1


theorem VertexLinkStarAdjacent.right_mem
    (K : Triangulation)
    (v x : Nat)
    (σ ρ : LinkTriangle)
    (h :
      VertexLinkStarAdjacent K v x σ ρ) :
    ρ ∈ vertexLinkStarTriangles K v x :=
  h.2.1


def VertexLinkStarConnected
    (K : Triangulation)
    (v x : Nat) : Prop :=
  ∀ σ ∈ vertexLinkStarTriangles K v x,
    ∀ ρ ∈ vertexLinkStarTriangles K v x,
      Relation.ReflTransGen
        (VertexLinkStarAdjacent K v x)
        σ ρ


def VertexLinkStarDegreeTwo
    (K : Triangulation)
    (v x : Nat) : Prop :=
  ∀ σ ∈ vertexLinkStarTriangles K v x,
    ∃ ρ₁ ρ₂ : LinkTriangle,
      ρ₁ ≠ σ ∧
      ρ₂ ≠ σ ∧
      ρ₁ ≠ ρ₂ ∧
      VertexLinkStarAdjacent K v x σ ρ₁ ∧
      VertexLinkStarAdjacent K v x σ ρ₂ ∧
      ∀ ρ : LinkTriangle,
        ρ ≠ σ →
        VertexLinkStarAdjacent K v x σ ρ →
        ρ = ρ₁ ∨ ρ = ρ₂




def VertexLinkLocallyConnected
    (K : Triangulation)
    (v : Nat) : Prop :=
  ∀ x : Nat,
    VertexLinkVertexRepresented K v x →
      VertexLinkStarConnected K v x


def VertexLinksLocallyConnected
    (K : Triangulation) : Prop :=
  ∀ v ∈ vertexSupport K,
    VertexLinkLocallyConnected K v


end Poincare
