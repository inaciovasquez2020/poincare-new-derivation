import Poincare.PositionalStellarSpokeBlocker
import Mathlib.Tactic

namespace Poincare

/-- Every (possibly repeated-label) triangular face represented by the
tetrahedron to be subdivided is represented by one of its four stellar
tetrahedra. This is finite combinatorial coverage, not a global
topological claim. -/
theorem Move41Site.targetTet_triangle_covered_by_source
    (s : Move41Site) (x y z : Nat)
    (hx : x ∈ s.targetTet.verts)
    (hy : y ∈ s.targetTet.verts)
    (hz : z ∈ s.targetTet.verts) :
    ∃ τ ∈ s.sourceTets,
      x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts := by
  simp only [Move41Site.targetTet, Tet.verts,
    List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl <;>
    simp [Move41Site.sourceTets, Move41Site.sourceTet₀,
      Move41Site.sourceTet₁, Move41Site.sourceTet₂,
      Move41Site.sourceTet₃, Tet.verts]

/-- The original represented triangles persist after positional 1→4 insertion.
No closed-core or center-freshness hypothesis beyond those required to name
the literal insertion is used. -/
theorem Move41Site.insertFreshAt_old_triangle_persists
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K)
    (x y z : Nat)
    (hrep : ∃ τ ∈ K.tets,
       x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts) :
    ∃ τ ∈ (s.insertFreshAt K before after hsource hfresh).tets,
      x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts := by
  obtain ⟨τ, hτ, hx, hy, hz⟩ := hrep
  have hτ' : τ ∈ before ++ s.targetTet :: after := by
    rw [← hsource]
    exact hτ
  rcases List.mem_append.mp hτ' with hb | ha
  · exact ⟨τ, by
      change τ ∈ before ++ s.sourceTets ++ after
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hb))), hx, hy, hz⟩
  · rcases List.mem_cons.mp ha with htarget | hafter
    · subst τ
      obtain ⟨ρ, hρ, hrx, hry, hrz⟩ :=
        s.targetTet_triangle_covered_by_source x y z hx hy hz
      exact ⟨ρ, by
        change ρ ∈ before ++ s.sourceTets ++ after
        exact List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inr hρ))), hrx, hry, hrz⟩
    · exact ⟨τ, by
        change τ ∈ before ++ s.sourceTets ++ after
        exact List.mem_append.mpr (Or.inr hafter), hx, hy, hz⟩

/-- If a 3→2 candidate's complementary face is absent after a fresh
positional stellar insertion, then that same face was already absent
before insertion. Thus stellar subdivision never deletes a represented
triangle that could make the SourceFaceAbsent clause newly true. -/
theorem Move41Site.insertFreshAt_sourceFaceAbsent_implies_original
    (s : Move41Site) (m : Move32Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hfresh : s.e ∉ vertexSupport K)
    (habs : m.SourceFaceAbsent
      (s.insertFreshAt K before after hsource hfresh)) :
    m.SourceFaceAbsent K := by
  intro τ hτ hface
  obtain ⟨ρ, hρ, hrx, hry, hrz⟩ :=
    s.insertFreshAt_old_triangle_persists K before after
      hsource hfresh m.a m.b m.c ⟨τ, hτ, hface⟩
  exact habs ρ hρ ⟨hrx, hry, hrz⟩

end Poincare
