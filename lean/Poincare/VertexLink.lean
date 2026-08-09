import Poincare.Validity
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching

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
deriving DecidableEq


def LinkEdge.ofDistinct
    (a b : Nat)
    (hne : a ≠ b) : LinkEdge :=
  if hab : a < b then
    ⟨a, b, hab⟩
  else
    ⟨b, a,
      Nat.lt_of_le_of_ne
        (Nat.le_of_not_gt hab)
        (Ne.symm hne)⟩


theorem LinkEdge.ofDistinct_symm
    (a b : Nat)
    (hne : a ≠ b) :
    LinkEdge.ofDistinct a b hne =
      LinkEdge.ofDistinct b a (Ne.symm hne) := by

  by_cases hab : a < b

  · have hba : ¬ b < a := by
      exact lt_asymm hab

    simp [
      LinkEdge.ofDistinct,
      hab,
      hba
    ]

  · have hba : b < a :=
      Nat.lt_of_le_of_ne
        (Nat.le_of_not_gt hab)
        (Ne.symm hne)

    simp [
      LinkEdge.ofDistinct,
      hab,
      hba
    ]


def LinkEdge.InTriangle
    (e : LinkEdge)
    (σ : LinkTriangle) : Prop :=
  e.lo ∈ σ.verts ∧
  e.hi ∈ σ.verts

theorem LinkEdge.ofDistinct_inTriangle
    (σ : LinkTriangle)
    (a b : Nat)
    (hne : a ≠ b)
    (ha : a ∈ σ.verts)
    (hb : b ∈ σ.verts) :
    (LinkEdge.ofDistinct a b hne).InTriangle σ := by

  unfold LinkEdge.ofDistinct
  split
  · exact ⟨ha, hb⟩
  · exact ⟨hb, ha⟩


def LinkTriangle.edges
    (σ : LinkTriangle)
    (hσ : σ.verts.Nodup) :
    List LinkEdge := by

  rcases σ with ⟨a, b, c⟩

  have h :
      (a ≠ b ∧ a ≠ c) ∧
      b ≠ c := by
    simpa [LinkTriangle.verts] using hσ

  exact [
    LinkEdge.ofDistinct a b h.1.1,
    LinkEdge.ofDistinct a c h.1.2,
    LinkEdge.ofDistinct b c h.2
  ]


@[simp]
theorem LinkTriangle.edges_length
    (σ : LinkTriangle)
    (hσ : σ.verts.Nodup) :
    (σ.edges hσ).length = 3 := by

  rcases σ with ⟨a, b, c⟩
  simp [LinkTriangle.edges]


theorem LinkTriangle.mem_edges_inTriangle
    (σ : LinkTriangle)
    (hσ : σ.verts.Nodup)
    (e : LinkEdge)
    (he : e ∈ σ.edges hσ) :
    e.InTriangle σ := by

  rcases σ with ⟨a, b, c⟩

  simp only [
    LinkTriangle.edges,
    List.mem_cons
  ] at he

  rcases he with he | he

  · subst e
    apply LinkEdge.ofDistinct_inTriangle
    · simp [LinkTriangle.verts]
    · simp [LinkTriangle.verts]

  · rcases he with he | he

    · subst e
      apply LinkEdge.ofDistinct_inTriangle
      · simp [LinkTriangle.verts]
      · simp [LinkTriangle.verts]

    · rcases he with he | he

      · subst e
        apply LinkEdge.ofDistinct_inTriangle
        · simp [LinkTriangle.verts]
        · simp [LinkTriangle.verts]

      · simp at he


theorem LinkTriangle.inTriangle_mem_edges
    (σ : LinkTriangle)
    (hσ : σ.verts.Nodup)
    (e : LinkEdge)
    (he : e.InTriangle σ) :
    e ∈ σ.edges hσ := by

  rcases σ with ⟨a, b, c⟩
  rcases e with ⟨lo, hi, hlt⟩

  simp [
    LinkEdge.InTriangle,
    LinkTriangle.verts
  ] at he

  rcases he with ⟨hlo, hhi⟩

  rcases hlo with rfl | rfl | rfl

  · rcases hhi with rfl | rfl | rfl

    · exact (lt_irrefl _ hlt).elim

    · simp [
        LinkTriangle.edges,
        LinkEdge.ofDistinct,
        hlt,
        lt_asymm hlt
      ]

    · simp [
        LinkTriangle.edges,
        LinkEdge.ofDistinct,
        hlt,
        lt_asymm hlt
      ]

  · rcases hhi with rfl | rfl | rfl

    · simp [
        LinkTriangle.edges,
        LinkEdge.ofDistinct,
        hlt,
        lt_asymm hlt
      ]

    · exact (lt_irrefl _ hlt).elim

    · simp [
        LinkTriangle.edges,
        LinkEdge.ofDistinct,
        hlt,
        lt_asymm hlt
      ]

  · rcases hhi with rfl | rfl | rfl

    · simp [
        LinkTriangle.edges,
        LinkEdge.ofDistinct,
        hlt,
        lt_asymm hlt
      ]

    · simp [
        LinkTriangle.edges,
        LinkEdge.ofDistinct,
        hlt,
        lt_asymm hlt
      ]

    · exact (lt_irrefl _ hlt).elim


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


def vertexLinkEdges
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat) :
    List LinkEdge :=
  ((vertexLinkTriangles K v).attach.flatMap
    (fun σ =>
      σ.1.edges
        (vertexLinkTriangles_triangle_nodup
          K hcore v σ.1 σ.2))).eraseDups


theorem mem_vertexLinkEdges_represented
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : LinkEdge)
    (he : e ∈ vertexLinkEdges K hcore v) :
    e.RepresentedAt K v := by

  rw [
    vertexLinkEdges,
    List.mem_eraseDups,
    List.mem_flatMap
  ] at he

  rcases he with ⟨σ, _, heσ⟩

  refine ⟨σ.1, σ.2, ?_⟩

  exact
    LinkTriangle.mem_edges_inTriangle
      σ.1
      (vertexLinkTriangles_triangle_nodup
        K hcore v σ.1 σ.2)
      e
      heσ


theorem represented_mem_vertexLinkEdges
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : LinkEdge)
    (hrep : e.RepresentedAt K v) :
    e ∈ vertexLinkEdges K hcore v := by

  rcases hrep with ⟨σ, hσ, heσ⟩

  rw [
    vertexLinkEdges,
    List.mem_eraseDups,
    List.mem_flatMap
  ]

  refine
    ⟨⟨σ, hσ⟩, ?_, ?_⟩

  · simp

  · exact
      LinkTriangle.inTriangle_mem_edges
        σ
        (vertexLinkTriangles_triangle_nodup
          K hcore v σ hσ)
        e
        heσ


theorem mem_vertexLinkEdges_iff
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : LinkEdge) :
    e ∈ vertexLinkEdges K hcore v ↔
      e.RepresentedAt K v := by

  constructor

  · exact
      mem_vertexLinkEdges_represented
        K hcore v e

  · exact
      represented_mem_vertexLinkEdges
        K hcore v e


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


theorem vertexLinkTriangles_nodup
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat) :
    (vertexLinkTriangles K v).Nodup := by
  unfold vertexLinkTriangles

  apply
    (hcore.2.1.filterMap
      (fun τ => τ.linkTriangleAt? v))

  intro τ ρ hnotSame
  intro σ hστ
  intro ψ hψρ
  intro hσψ

  have hτExtract :
      τ.linkTriangleAt? v = some σ := by
    simpa using hστ

  have hρExtract :
      ρ.linkTriangleAt? v = some ψ := by
    simpa using hψρ

  subst ψ

  apply hnotSame

  intro y
  by_cases hyv : y = v

  · subst y

    have hvτ :
        v ∈ τ.verts := by
      rw [← τ.linkTriangleAt?_isSome_iff v]
      simp [hτExtract]

    have hvρ :
        v ∈ ρ.verts := by
      rw [← ρ.linkTriangleAt?_isSome_iff v]
      simp [hρExtract]

    exact ⟨fun _ => hvρ, fun _ => hvτ⟩

  · constructor

    · intro hyτ

      have hyσ :
          y ∈ σ.verts :=
        (τ.mem_linkTriangleAt?_iff
          v y σ hτExtract hyv).2 hyτ

      exact
        (ρ.mem_linkTriangleAt?_iff
          v y σ hρExtract hyv).1 hyσ

    · intro hyρ

      have hyσ :
          y ∈ σ.verts :=
        (ρ.mem_linkTriangleAt?_iff
          v y σ hρExtract hyv).2 hyρ

      exact
        (τ.mem_linkTriangleAt?_iff
          v y σ hτExtract hyv).1 hyσ




theorem vertexLinkTriangles_pairwise_vertexSet_ne
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat) :
    (vertexLinkTriangles K v).Pairwise
      (fun σ ρ =>
        ¬ ∀ y : Nat,
            y ∈ σ.verts ↔
            y ∈ ρ.verts) := by
  unfold vertexLinkTriangles

  apply
    hcore.2.1.filterMap
      (fun τ => τ.linkTriangleAt? v)

  intro τ ρ hnotSame
  intro σ hτExtract
  intro ψ hρExtract
  intro hsame

  apply hnotSame

  intro y
  by_cases hyv : y = v

  · subst y

    have hvτ :
        v ∈ τ.verts := by
      rw [← τ.linkTriangleAt?_isSome_iff v]
      simp [hτExtract]

    have hvρ :
        v ∈ ρ.verts := by
      rw [← ρ.linkTriangleAt?_isSome_iff v]
      simp [hρExtract]

    exact
      ⟨fun _ => hvρ,
       fun _ => hvτ⟩

  · constructor

    · intro hyτ

      have hyσ :
          y ∈ σ.verts :=
        (τ.mem_linkTriangleAt?_iff
          v y σ hτExtract hyv).2 hyτ

      have hyψ :
          y ∈ ψ.verts :=
        (hsame y).1 hyσ

      exact
        (ρ.mem_linkTriangleAt?_iff
          v y ψ hρExtract hyv).1 hyψ

    · intro hyρ

      have hyψ :
          y ∈ ψ.verts :=
        (ρ.mem_linkTriangleAt?_iff
          v y ψ hρExtract hyv).2 hyρ

      have hyσ :
          y ∈ σ.verts :=
        (hsame y).2 hyψ

      exact
        (τ.mem_linkTriangleAt?_iff
          v y σ hτExtract hyv).1 hyσ




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


def vertexLinkVertices
    (K : Triangulation)
    (v : Nat) : List Nat :=
  ((vertexLinkTriangles K v).flatMap
    LinkTriangle.verts).eraseDups


theorem mem_vertexLinkVertices_iff
    (K : Triangulation)
    (v x : Nat) :
    x ∈ vertexLinkVertices K v ↔
      VertexLinkVertexRepresented K v x := by
  simp [
    vertexLinkVertices,
    VertexLinkVertexRepresented
  ]


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


instance instFiniteVertexLinkStarCarrier
    (K : Triangulation)
    (v x : Nat) :
    Finite
      {σ : LinkTriangle //
        σ ∈ vertexLinkStarTriangles K v x} := by
  letI :
      Fintype
        {σ : LinkTriangle //
          σ ∈ vertexLinkStarTriangles K v x} :=
    Fintype.ofFinset
      (vertexLinkStarTriangles K v x).toFinset
      (by
        intro σ
        exact List.mem_toFinset)
  infer_instance


def vertexLinkStarGraph
    (K : Triangulation)
    (v x : Nat) :
    SimpleGraph
      {σ : LinkTriangle //
        σ ∈ vertexLinkStarTriangles K v x} :=
  SimpleGraph.fromRel
    (fun σ ρ =>
      VertexLinkStarAdjacent
        K v x σ.1 ρ.1)




@[simp]
theorem vertexLinkStarGraph_adj
    (K : Triangulation)
    (v x : Nat)
    (σ ρ :
      {τ : LinkTriangle //
        τ ∈ vertexLinkStarTriangles K v x}) :
    (vertexLinkStarGraph K v x).Adj σ ρ ↔
      σ ≠ ρ ∧
      VertexLinkStarAdjacent K v x σ.1 ρ.1 := by
  rw [vertexLinkStarGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact
        ⟨hne,
         VertexLinkStarAdjacent.symm
           K v x ρ.1 σ.1 h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩




def VertexLinkStarConnected
    (K : Triangulation)
    (v x : Nat) : Prop :=
  ∀ σ ∈ vertexLinkStarTriangles K v x,
    ∀ ρ ∈ vertexLinkStarTriangles K v x,
      Relation.ReflTransGen
        (VertexLinkStarAdjacent K v x)
        σ ρ


theorem VertexLinkStarConnected.preconnected
    (K : Triangulation)
    (v x : Nat)
    (hconn : VertexLinkStarConnected K v x) :
    (vertexLinkStarGraph K v x).Preconnected := by
  intro σ ρ

  have lift :
      ∀ {a b : LinkTriangle},
        Relation.ReflTransGen
            (VertexLinkStarAdjacent K v x)
            a b →
        ∀ (ha : a ∈ vertexLinkStarTriangles K v x)
          (hb : b ∈ vertexLinkStarTriangles K v x),
          (vertexLinkStarGraph K v x).Reachable
            ⟨a, ha⟩
            ⟨b, hb⟩ := by
    intro a b hpath
    induction hpath with
    | refl =>
        intro ha hb
        have heq :
            (⟨a, ha⟩ :
              {τ : LinkTriangle //
                τ ∈ vertexLinkStarTriangles K v x}) =
            ⟨a, hb⟩ := by
          have hp : ha = hb :=
            Subsingleton.elim ha hb
          cases hp
          rfl
        rw [← heq]
    | tail hprev hstep ih =>
        intro ha hc

        have hmid :
            _ ∈ vertexLinkStarTriangles K v x :=
          VertexLinkStarAdjacent.left_mem
            K v x _ _ hstep

        let mid :
            {τ : LinkTriangle //
              τ ∈ vertexLinkStarTriangles K v x} :=
          ⟨_, hmid⟩

        let finish :
            {τ : LinkTriangle //
              τ ∈ vertexLinkStarTriangles K v x} :=
          ⟨_, hc⟩

        have hreachMid :
            (vertexLinkStarGraph K v x).Reachable
              ⟨a, ha⟩ mid := by
          exact ih ha hmid

        have hreachStep :
            (vertexLinkStarGraph K v x).Reachable
              mid finish := by
          by_cases heq : mid = finish
          · rw [heq]
          · apply SimpleGraph.Adj.reachable
            rw [vertexLinkStarGraph_adj]
            exact ⟨heq, hstep⟩

        exact
          SimpleGraph.Reachable.trans
            hreachMid
            hreachStep

  exact
    lift
      (hconn σ.1 σ.2 ρ.1 ρ.2)
      σ.2
      ρ.2




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




theorem VertexLinkStarDegreeTwo.isCycles
    (K : Triangulation)
    (v x : Nat)
    (hdeg : VertexLinkStarDegreeTwo K v x) :
    (vertexLinkStarGraph K v x).IsCycles := by
  intro σ _
  obtain
    ⟨ρ₁, ρ₂,
      hρ₁σ, hρ₂σ, hρ₁ρ₂,
      hσρ₁, hσρ₂, hall⟩ :=
    hdeg σ.1 σ.2

  have hρ₁mem :
      ρ₁ ∈ vertexLinkStarTriangles K v x :=
    VertexLinkStarAdjacent.right_mem
      K v x σ.1 ρ₁ hσρ₁

  have hρ₂mem :
      ρ₂ ∈ vertexLinkStarTriangles K v x :=
    VertexLinkStarAdjacent.right_mem
      K v x σ.1 ρ₂ hσρ₂

  let r₁ :
      {τ : LinkTriangle //
        τ ∈ vertexLinkStarTriangles K v x} :=
    ⟨ρ₁, hρ₁mem⟩

  let r₂ :
      {τ : LinkTriangle //
        τ ∈ vertexLinkStarTriangles K v x} :=
    ⟨ρ₂, hρ₂mem⟩

  have hr₁σ : r₁ ≠ σ := by
    intro heq
    apply hρ₁σ
    exact congrArg Subtype.val heq

  have hr₂σ : r₂ ≠ σ := by
    intro heq
    apply hρ₂σ
    exact congrArg Subtype.val heq

  have hr₁r₂ : r₁ ≠ r₂ := by
    intro heq
    apply hρ₁ρ₂
    exact congrArg Subtype.val heq

  have hneighbors :
      (vertexLinkStarGraph K v x).neighborSet σ =
        {r₁, r₂} := by
    ext ρ
    simp only [
      SimpleGraph.mem_neighborSet,
      vertexLinkStarGraph_adj,
      Set.mem_insert_iff,
      Set.mem_singleton_iff
    ]
    constructor
    · rintro ⟨hσρ, hstar⟩
      have hval :
          ρ.1 ≠ σ.1 := by
        intro heq
        apply hσρ
        apply Subtype.ext
        exact heq.symm
      rcases hall ρ.1 hval hstar with h | h
      · left
        apply Subtype.ext
        exact h
      · right
        apply Subtype.ext
        exact h
    · intro h
      rcases h with h | h
      · subst ρ
        exact ⟨hr₁σ.symm, hσρ₁⟩
      · subst ρ
        exact ⟨hr₂σ.symm, hσρ₂⟩

  rw [hneighbors]
  simp [hr₁r₂]




theorem exists_vertexLinkStar_coveringCycle
    (K : Triangulation)
    (v x : Nat)
    (hrep : VertexLinkVertexRepresented K v x)
    (hconn : VertexLinkStarConnected K v x)
    (hdeg : VertexLinkStarDegreeTwo K v x) :
    ∃
      (σ :
        {τ : LinkTriangle //
          τ ∈ vertexLinkStarTriangles K v x}),
      ∃
        (p :
          (vertexLinkStarGraph K v x).Walk σ σ),
        p.IsCycle ∧
        p.toSubgraph.verts =
          (Set.univ :
            Set
              {τ : LinkTriangle //
                τ ∈ vertexLinkStarTriangles K v x}) := by

  obtain ⟨σ, hσ⟩ :=
    (vertexLinkVertexRepresented_iff_star_nonempty
      K v x).1 hrep

  let s :
      {τ : LinkTriangle //
        τ ∈ vertexLinkStarTriangles K v x} :=
    ⟨σ, hσ⟩

  have hpre :
      (vertexLinkStarGraph K v x).Preconnected :=
    VertexLinkStarConnected.preconnected
      K v x hconn

  have hcycles :
      (vertexLinkStarGraph K v x).IsCycles :=
    VertexLinkStarDegreeTwo.isCycles
      K v x hdeg

  obtain
    ⟨ρ₁, ρ₂,
      hρ₁σ, hρ₂σ, hρ₁ρ₂,
      hσρ₁, hσρ₂, hall⟩ :=
    hdeg σ hσ

  have hρ₁mem :
      ρ₁ ∈ vertexLinkStarTriangles K v x :=
    VertexLinkStarAdjacent.right_mem
      K v x σ ρ₁ hσρ₁

  let r₁ :
      {τ : LinkTriangle //
        τ ∈ vertexLinkStarTriangles K v x} :=
    ⟨ρ₁, hρ₁mem⟩

  have hsr₁ : s ≠ r₁ := by
    intro heq
    apply hρ₁σ
    exact (congrArg Subtype.val heq).symm

  have hn :
      ((vertexLinkStarGraph K v x).neighborSet s).Nonempty := by
    refine ⟨r₁, ?_⟩
    rw [
      SimpleGraph.mem_neighborSet,
      vertexLinkStarGraph_adj
    ]
    exact ⟨hsr₁, hσρ₁⟩

  have hsupp :
      ((vertexLinkStarGraph K v x).connectedComponentMk s).supp =
        (Set.univ :
          Set
            {τ : LinkTriangle //
              τ ∈ vertexLinkStarTriangles K v x}) := by
    apply Set.eq_univ_of_forall
    intro t
    rw [
      SimpleGraph.ConnectedComponent.mem_supp_iff
    ]
    exact
      SimpleGraph.ConnectedComponent.sound
        (hpre t s)

  obtain ⟨p, hpCycle, hpVerts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c :=
        (vertexLinkStarGraph K v x).connectedComponentMk s)
      (v := s)
      (by
        exact
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
      hn

  refine ⟨s, p, hpCycle, ?_⟩
  rw [hpVerts, hsupp]




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



def VertexLinkClosedSurfaceCertificate
    (K : Triangulation)
    (v : Nat) : Prop :=
  (∀ σ ∈ vertexLinkTriangles K v,
      σ.verts.Nodup) ∧

  (vertexLinkTriangles K v).Pairwise
    (fun σ ρ =>
      ¬ ∀ y : Nat,
          y ∈ σ.verts ↔
          y ∈ ρ.verts) ∧

  (∀ e : LinkEdge,
      e.RepresentedAt K v →
        ((vertexLinkTriangles K v).filter
          (fun σ => decide (e.InTriangle σ))).length = 2) ∧

  ∀ x : Nat,
    VertexLinkVertexRepresented K v x →
      ∃
        (σ :
          {τ : LinkTriangle //
            τ ∈ vertexLinkStarTriangles K v x}),
        ∃
          (p :
            (vertexLinkStarGraph K v x).Walk σ σ),
          p.IsCycle ∧
          p.toSubgraph.verts =
            (Set.univ :
              Set
                {τ : LinkTriangle //
                  τ ∈ vertexLinkStarTriangles K v x})


theorem vertexLinkClosedSurfaceCertificate_of_closedCore
    (K : Triangulation)
    (v : Nat)
    (hcore : ClosedTriangulationCore K)
    (hlocal : VertexLinkLocallyConnected K v)
    (hdeg :
      ∀ x : Nat,
        VertexLinkVertexRepresented K v x →
          VertexLinkStarDegreeTwo K v x) :
    VertexLinkClosedSurfaceCertificate K v := by

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro σ hσ
    exact
      vertexLinkTriangles_triangle_nodup
        K hcore v σ hσ

  · exact
      vertexLinkTriangles_pairwise_vertexSet_ne
        K hcore v

  · intro e hrep
    exact
      represented_linkEdge_link_incidence_two
        K hcore v e hrep

  · intro x hrep
    exact
      exists_vertexLinkStar_coveringCycle
        K v x
        hrep
        (hlocal x hrep)
        (hdeg x hrep)



def VertexLinkConnectedClosedSurfaceCertificate
    (K : Triangulation)
    (v : Nat) : Prop :=
  VertexLinkClosedSurfaceCertificate K v ∧
  VertexLinkConnected K v


theorem connectedLinkClosedCore_vertexLinks_connectedClosedSurfaceCertificate
    (K : Triangulation)
    (hconnected : ConnectedLinkClosedCore K)
    (hlocal : VertexLinksLocallyConnected K)
    (hdeg :
      ∀ v ∈ vertexSupport K,
        ∀ x : Nat,
          VertexLinkVertexRepresented K v x →
            VertexLinkStarDegreeTwo K v x) :
    ∀ v ∈ vertexSupport K,
      VertexLinkConnectedClosedSurfaceCertificate K v := by

  intro v hv

  refine ⟨?_, ?_⟩

  · exact
      vertexLinkClosedSurfaceCertificate_of_closedCore
        K v
        (ConnectedLinkClosedCore.closedCore
          K hconnected)
        (hlocal v hv)
        (hdeg v hv)

  · exact
      ConnectedLinkClosedCore.vertexLinkConnected
        K hconnected v hv


end Poincare
