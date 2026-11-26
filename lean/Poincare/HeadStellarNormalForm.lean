import Poincare.StabilizedFinitePathDescent

namespace Poincare

/-!
# Canonical head-tetrahedron stellar subdivision

This module constructs the four actual `Tet` records of a 1→4 stellar
subdivision in the repository's list representation. The canonical 4→1
replacement recovers the original list *exactly*, not merely as an unordered
set. Freshness of the new center in the unchanged exterior certifies that
its complete tetrahedron star lies in the four inserted tetrahedra.

The subdivision preserves the closed core and certifies a `1 → 4` step
when the center is fresh in the unchanged tetrahedra.
-/

/-- Four distinct source tetrahedra in the order that the repository's
`Move41Site.unchangedTets` algorithm erases them. -/
def Move41Site.headStellar (s : Move41Site) (rest : List Tet) : Triangulation :=
  { tets := s.sourceTet₀ :: s.sourceTet₁ :: s.sourceTet₂ :: s.sourceTet₃ :: rest }

/-- The canonical 4→1 replacement of the explicit head subdivision recovers
the original tetrahedron list, with its ordering unchanged. -/
theorem Move41Site.replace_headStellar_exact
    (s : Move41Site) (rest : List Tet) :
    s.replace (s.headStellar rest) =
      { tets := s.targetTet :: rest } := by
  have hself (τ : Tet) : sameTetVerticesBool τ τ = true :=
    (sameTetVerticesBool_eq_true_iff τ τ).2 (fun _ => Iff.rfl)
  simp [Move41Site.replace, Move41Site.unchangedTets,
    Move41Site.headStellar, eraseFirstSameTet, hself]

/-- If the center vertex is absent from the unchanged exterior, every
tetrahedron containing it in the constructed subdivision belongs to
the four-tetrahedron stellar star. No closed-core claim is used. -/
theorem Move41Site.headStellar_center_saturated
    (s : Move41Site) (rest : List Tet)
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    ∀ τ ∈ (s.headStellar rest).tets,
      s.e ∈ τ.verts →
      ∃ ρ ∈ s.sourceTets, SameTetVertices τ ρ := by
  intro τ hmem hcenter
  simp only [Move41Site.headStellar, List.mem_cons] at hmem
  rcases hmem with h0 | h1 | h2 | h3 | hrest
  · subst τ
    exact ⟨s.sourceTet₀, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · subst τ
    exact ⟨s.sourceTet₁, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · subst τ
    exact ⟨s.sourceTet₂, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · subst τ
    exact ⟨s.sourceTet₃, by simp [Move41Site.sourceTets], fun _ => Iff.rfl⟩
  · exact False.elim ((hfresh τ hrest) hcenter)

/-- The actual `Move41Site` for a subdivision of a specific tetrahedron
with an explicitly distinct new vertex. -/
def Tet.freshStellarSite
    (τ : Tet) (x : Nat)
    (hdist : [τ.v0, τ.v1, τ.v2, τ.v3, x].Nodup) : Move41Site :=
  { a := τ.v0, b := τ.v1, c := τ.v2, d := τ.v3, e := x,
    distinct := hdist }

@[simp] theorem Tet.freshStellarSite_target
    (τ : Tet) (x : Nat)
    (hdist : [τ.v0, τ.v1, τ.v2, τ.v3, x].Nodup) :
    (τ.freshStellarSite x hdist).targetTet = τ := by
  cases τ
  rfl

/-- An explicitly fresh subdivision of the first tetrahedron is an exact
predecessor of the original *list-valued* triangulation. -/
theorem Tet.freshHeadStellar_replace_exact
    (τ : Tet) (x : Nat)
    (hdist : [τ.v0, τ.v1, τ.v2, τ.v3, x].Nodup)
    (rest : List Tet) :
    (τ.freshStellarSite x hdist).replace
      ((τ.freshStellarSite x hdist).headStellar rest) =
      ({ tets := τ :: rest } : Triangulation) := by
  rw [Move41Site.replace_headStellar_exact]
  simp

private theorem Move41Site.sourceVertsNodup (s : Move41Site) :
    ∀ τ ∈ s.sourceTets, τ.verts.Nodup := by
  intro τ hτ
  have hd := s.distinct
  simp [Move41Site.sourceTets] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;>
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]

private theorem Move41Site.sourceCenter (s : Move41Site) :
    ∀ τ ∈ s.sourceTets, s.e ∈ τ.verts := by
  intro τ hτ
  simp [Move41Site.sourceTets] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;>
    simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]

theorem Move41Site.sourceDistinct (s : Move41Site) :
    s.sourceTets.Pairwise (fun τ σ => ¬ SameTetVertices τ σ) := by
  simp [Move41Site.sourceTets]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  all_goals intro h
  · have hc := h s.c
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₁, Tet.verts, eq_comm]
  · have hb := h s.b
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₂, Tet.verts, eq_comm]
  · have ha := h s.a
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₀, Move41Site.sourceTet₃, Tet.verts, eq_comm]
  · have hb := h s.b
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₁, Move41Site.sourceTet₂, Tet.verts, eq_comm]
  · have ha := h s.a
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₁, Move41Site.sourceTet₃, Tet.verts, eq_comm]
  · have ha := h s.a
    have hd := s.distinct
    simp_all [Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts, eq_comm]

set_option maxHeartbeats 10000000 in
private theorem Move41Site.stellarLocalIncidence (s : Move41Site)
    (x y z : Nat) (hxyz : [x, y, z].Nodup)
    (hx : x ∈ [s.a, s.b, s.c, s.d, s.e])
    (hy : y ∈ [s.a, s.b, s.c, s.d, s.e])
    (hz : z ∈ [s.a, s.b, s.c, s.d, s.e]) :
    let p := fun τ : Tet => decide (x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts)
    if s.e ∈ [x, y, z] then (s.sourceTets.filter p).length = 2
    else (s.sourceTets.filter p).length = ([s.targetTet].filter p).length := by
  have hd := s.distinct
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Move41Site.sourceTets, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
      Move41Site.sourceTet₂, Move41Site.sourceTet₃, Move41Site.targetTet, Tet.verts, eq_comm]

/-- Subdividing the head tetrahedron at a center fresh in the exterior
preserves nondegeneracy, distinct tetrahedra, and two-fold face incidence. -/
theorem Move41Site.headStellar_closedCore (s : Move41Site) (rest : List Tet)
    (hcore : ClosedTriangulationCore { tets := s.targetTet :: rest })
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    ClosedTriangulationCore (s.headStellar rest) := by
  change ClosedTriangulationCore { tets := s.sourceTets ++ rest }
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    rcases List.mem_append.mp hτ with hs | hr
    · exact s.sourceVertsNodup τ hs
    · exact hcore.1 τ (List.mem_cons_of_mem _ hr)
  · apply List.pairwise_append.mpr
    refine ⟨s.sourceDistinct, (List.pairwise_cons.mp hcore.2.1).2, ?_⟩
    intro τ hs σ hr hsame
    exact hfresh σ hr ((hsame s.e).mp (s.sourceCenter τ hs))
  · intro x y z hxyz hrepresented
    let p := fun τ : Tet => decide (x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts)
    change ((s.sourceTets ++ rest).filter p).length = 2
    have labels (τ : Tet) (hτ : τ ∈ s.targetTet :: s.sourceTets)
        (v : Nat) (hv : v ∈ τ.verts) : v ∈ [s.a, s.b, s.c, s.d, s.e] := by
      simp [Move41Site.sourceTets] at hτ
      rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
        simp [Move41Site.targetTet, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
          Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts] at hv ⊢ <;> tauto
    have localTable (τ : Tet) (hτ : τ ∈ s.targetTet :: s.sourceTets)
        (hp : x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts) :
        if s.e ∈ [x, y, z] then (s.sourceTets.filter p).length = 2
        else (s.sourceTets.filter p).length = ([s.targetTet].filter p).length :=
      s.stellarLocalIncidence x y z hxyz
        (labels τ hτ x hp.1) (labels τ hτ y hp.2.1) (labels τ hτ z hp.2.2)
    rw [List.filter_append, List.length_append]
    by_cases he : s.e ∈ [x, y, z]
    · have noRest (τ : Tet) (hτ : τ ∈ rest) :
          ¬ (x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts) := by
        intro hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with h | h | h
        · exact hfresh τ hτ (h ▸ hp.1)
        · exact hfresh τ hτ (h ▸ hp.2.1)
        · exact hfresh τ hτ (h ▸ hp.2.2)
      have hrest : rest.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro τ hτ
        simp [p, noRest τ hτ]
      obtain ⟨τ, hτ, hp⟩ := hrepresented
      rcases List.mem_append.mp hτ with hs | hr
      · simpa [he, hrest] using localTable τ (List.mem_cons_of_mem _ hs) hp
      · exact (noRest τ hr hp).elim
    · have hcounts :
          (s.sourceTets.filter p).length = ([s.targetTet].filter p).length := by
        by_cases hlocal : ∃ τ ∈ s.targetTet :: s.sourceTets, p τ = true
        · obtain ⟨τ, hτ, hp⟩ := hlocal
          simpa [he] using localTable τ hτ (of_decide_eq_true hp)
        · have emptyFilter (L : List Tet) (hsub : ∀ τ ∈ L,
              τ ∈ s.targetTet :: s.sourceTets) : L.filter p = [] := by
            rw [List.filter_eq_nil_iff]
            intro τ hτ
            exact fun hp => hlocal ⟨τ, hsub τ hτ, hp⟩
          rw [emptyFilter s.sourceTets (fun τ hτ => List.mem_cons_of_mem _ hτ),
            emptyFilter [s.targetTet] (by simp)]
      have hold : ∃ τ ∈ s.targetTet :: rest,
          x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts := by
        obtain ⟨τ, hτ, hp⟩ := hrepresented
        rcases List.mem_append.mp hτ with hs | hr
        · have hmem : τ ∈ s.sourceTets.filter p :=
            List.mem_filter.mpr ⟨hs, decide_eq_true hp⟩
          have hpos := List.length_pos_iff_exists_mem.mpr ⟨τ, hmem⟩
          rw [hcounts] at hpos
          obtain ⟨σ, hσ⟩ := List.length_pos_iff_exists_mem.mp hpos
          obtain ⟨hσhead, hσp⟩ := List.mem_filter.mp hσ
          have hEq : σ = s.targetTet := by simpa using hσhead
          subst σ
          exact ⟨s.targetTet, by simp, of_decide_eq_true hσp⟩
        · exact ⟨τ, List.mem_cons_of_mem _ hr, hp⟩
      have htwo := hcore.2.2 x y z hxyz hold
      change (([s.targetTet] ++ rest).filter p).length = 2 at htwo
      rw [List.filter_append, List.length_append] at htwo
      rwa [hcounts]

private theorem filter_length_one_of_pairwise {α : Type} (p : α → Bool) (L : List α)
    (hpair : L.Pairwise (fun x y => ¬ (p x = true ∧ p y = true)))
    (hex : ∃ x ∈ L, p x = true) : (L.filter p).length = 1 := by
  induction L with
  | nil => simp at hex
  | cons x L ih =>
    obtain ⟨hx, hL⟩ := List.pairwise_cons.mp hpair
    cases hp : p x with
    | false =>
      apply (show (L.filter p).length = 1 → _ by simp [hp])
      apply ih hL
      simpa [hp] using hex
    | true =>
      have hnil : L.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        exact fun hpy => hx y hy ⟨hp, hpy⟩
      simp [hp, hnil]

/-- The canonical inverse is legal in the freshly subdivided core. -/
theorem Move41Site.headStellar_legal (s : Move41Site) (rest : List Tet)
    (hcore : ClosedTriangulationCore { tets := s.targetTet :: rest })
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    s.LegalIn (s.headStellar rest) := by
  have hnew := s.headStellar_closedCore rest hcore hfresh
  refine ⟨hnew, ?_, s.sourceDistinct, s.headStellar_center_saturated rest hfresh, ?_⟩
  · intro source hs
    apply filter_length_one_of_pairwise
    · apply hnew.2.1.imp
      intro τ σ hne hmatch
      have hτ := (sameTetVerticesBool_eq_true_iff τ source).mp hmatch.1
      have hσ := (sameTetVerticesBool_eq_true_iff σ source).mp hmatch.2
      exact hne (fun v => (hτ v).trans (hσ v).symm)
    · exact ⟨source, List.mem_append_left _ hs,
        (sameTetVerticesBool_eq_true_iff source source).mpr (fun _ => Iff.rfl)⟩
  · intro τ hτ hsame
    have hd := s.distinct
    have hnot : s.e ∉ s.targetTet.verts := by
      simp_all [Move41Site.targetTet, Tet.verts, eq_comm]
    change τ ∈ s.sourceTets ++ rest at hτ
    rcases List.mem_append.mp hτ with hs | hr
    · exact hnot ((hsame s.e).mp (s.sourceCenter τ hs))
    · exact (List.pairwise_cons.mp hcore.2.1).1 τ hr (sameTetVertices_symm hsame)

/-- A fresh stellar subdivision of the head gives a certified `1 → 4` step
from the original list-valued closed core. -/
theorem Tet.freshHeadStellar_certifiedMove14
    (τ : Tet) (x : Nat) (hdist : [τ.v0, τ.v1, τ.v2, τ.v3, x].Nodup)
    (rest : List Tet) (hcore : ClosedTriangulationCore { tets := τ :: rest })
    (hfresh : ∀ ρ ∈ rest, x ∉ ρ.verts) :
    CertifiedPachnerStep { tets := τ :: rest }
      ((τ.freshStellarSite x hdist).headStellar rest) := by
  let s := τ.freshStellarSite x hdist
  have hold : ClosedTriangulationCore { tets := s.targetTet :: rest } := by
    simpa [s] using hcore
  have hlegal := s.headStellar_legal rest hold hfresh
  have hstep := CertifiedPachnerStep.move14 hlegal.closedCore s hlegal
  rw [τ.freshHeadStellar_replace_exact x hdist rest] at hstep
  exact hstep

end Poincare
