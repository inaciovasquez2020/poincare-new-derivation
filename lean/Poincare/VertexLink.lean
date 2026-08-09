import Poincare.Validity

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

end Poincare
