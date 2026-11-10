import Poincare.StabilizedFinitePathDescent

namespace Poincare

/-!
# Canonical head-tetrahedron stellar subdivision

This module constructs the four actual `Tet` records of a 1→4 stellar
subdivision in the repository's list representation. The canonical 4→1
replacement recovers the original list *exactly*, not merely as an unordered
set. Freshness of the new center in the unchanged exterior certifies that
its complete tetrahedron star lies in the four inserted tetrahedra.

These are **structural** results. They do not assert `ClosedTriangulationCore`
preservation or `Move41Site.LegalIn` for the subdivision, and therefore do
not yet construct a `CertifiedPachnerStep.move14`.
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

end Poincare
