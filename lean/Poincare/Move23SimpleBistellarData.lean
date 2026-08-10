import Poincare.Validity

namespace Poincare

/-- In a closed triangulation, a represented tetrahedron is determined by its
vertex set. -/
theorem ClosedTriangulationCore.eq_of_mem_of_sameTetVertices
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {τ ρ : Tet}
    (hτK : τ ∈ K.tets)
    (hρK : ρ ∈ K.tets)
    (hsame : SameTetVertices τ ρ) :
    τ = ρ := by
  have aux : ∀ {l : List Tet},
      l.Pairwise (fun α β => ¬ SameTetVertices α β) →
      ∀ {α β : Tet}, α ∈ l → β ∈ l → SameTetVertices α β → α = β := by
    intro l hp
    induction l with
    | nil => simp
    | cons σ t ih =>
        rw [List.pairwise_cons] at hp
        rcases hp with ⟨hσ, ht⟩
        intro α β hα hβ hab
        simp only [List.mem_cons] at hα hβ
        rcases hα with rfl | hαt <;> rcases hβ with rfl | hβt
        · rfl
        · exact False.elim (hσ β hβt hab)
        · exact False.elim (hσ α hαt (fun v => (hab v).symm))
        · exact ih ht hαt hβt hab
  exact aux hcore.2.1 hτK hρK hsame

/-- The two source tetrahedra at a legal `2-3` site have different represented
occurrences. -/
theorem ClosedTriangulationCore.move23Site_source_tets_ne
    {K : Triangulation}
    (_hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    {τL τR : Tet}
    (_hτLK : τL ∈ K.tets)
    (hτL : SameTetVertices τL s.leftTet)
    (_hτRK : τR ∈ K.tets)
    (hτR : SameTetVertices τR s.rightTet) :
    τL ≠ τR := by
  intro heq
  subst τR
  apply s.leftTet_not_same_rightTet
  intro v
  exact (hτL v).symm.trans (hτR v)

/-- A legal `2-3` site in the current simple-complex representation supplies
the nondegenerate, uniquely represented local bistellar data. -/
theorem ClosedTriangulationCore.move23Site_simpleBistellarData
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    (hlegal : s.LegalIn K) :
    [s.a, s.b, s.c, s.d, s.e].Nodup ∧
    (∃! τL : Tet,
      τL ∈ K.tets ∧ SameTetVertices τL s.leftTet) ∧
    (∃! τR : Tet,
      τR ∈ K.tets ∧ SameTetVertices τR s.rightTet) ∧
    s.leftTet.verts.Nodup ∧
    s.rightTet.verts.Nodup ∧
    s.newTet₀.verts.Nodup ∧
    s.newTet₁.verts.Nodup ∧
    s.newTet₂.verts.Nodup := by
  have hfive := s.distinct
  rcases hlegal.1 with ⟨⟨τL, hτLK, hτL⟩, ⟨τR, hτRK, hτR⟩⟩
  have hleftUnique :
      ∃! σ : Tet, σ ∈ K.tets ∧ SameTetVertices σ s.leftTet := by
    refine ⟨τL, ⟨hτLK, hτL⟩, ?_⟩
    intro σ hσ
    exact hcore.eq_of_mem_of_sameTetVertices hσ.1 hτLK
      (fun v => (hσ.2 v).trans (hτL v).symm)
  have hrightUnique :
      ∃! σ : Tet, σ ∈ K.tets ∧ SameTetVertices σ s.rightTet := by
    refine ⟨τR, ⟨hτRK, hτR⟩, ?_⟩
    intro σ hσ
    exact hcore.eq_of_mem_of_sameTetVertices hσ.1 hτRK
      (fun v => (hσ.2 v).trans (hτR v).symm)
  have hleft : s.leftTet.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.leftTet, Tet.verts] at hf ⊢
    aesop
  have hright : s.rightTet.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.rightTet, Tet.verts] at hf ⊢
    aesop
  have hnew0 : s.newTet₀.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.newTet₀, Tet.verts] at hf ⊢
    aesop
  have hnew1 : s.newTet₁.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.newTet₁, Tet.verts] at hf ⊢
    aesop
  have hnew2 : s.newTet₂.verts.Nodup := by
    have hf := hfive
    simp [Move23Site.newTet₂, Tet.verts] at hf ⊢
    aesop
  exact ⟨hfive, hleftUnique, hrightUnique, hleft, hright,
    hnew0, hnew1, hnew2⟩

end Poincare
