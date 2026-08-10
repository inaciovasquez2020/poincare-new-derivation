import Poincare.Validity

namespace Poincare

/-- Three distinct vertices of a nondegenerate tetrahedron leave a unique
fourth vertex. -/
theorem Tet.exists_unique_complement_vertex
    (τ : Tet)
    (hτ : τ.verts.Nodup)
    {a b c : Nat}
    (habc : [a, b, c].Nodup)
    (ha : a ∈ τ.verts)
    (hb : b ∈ τ.verts)
    (hc : c ∈ τ.verts) :
    ∃! d : Nat,
      d ∈ τ.verts ∧
      d ≠ a ∧
      d ≠ b ∧
      d ≠ c := by
  classical
  let s := τ.verts.toFinset
  let t := [a, b, c].toFinset
  have htCard : t.card = 3 := by
    simpa [t] using List.toFinset_card_of_nodup habc
  have hsCard : s.card = 4 := by
    simpa [s, Tet.verts] using List.toFinset_card_of_nodup hτ
  have hts : t ⊆ s := by
    intro v hv
    simp only [t, List.mem_toFinset] at hv
    simp only [s, List.mem_toFinset]
    aesop
  have hcard : (s \ t).card = 1 := by
    rw [Finset.card_sdiff_of_subset hts, hsCard, htCard]
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcard
  refine ⟨d, ?_, ?_⟩
  · have : d ∈ s \ t := by simp [hd]
    simpa [s, t] using this
  · intro e he
    have : e ∈ s \ t := by simpa [s, t] using he
    simpa [hd] using this

/-- Tetrahedra containing the same three distinct vertices have different
complementary vertices when their vertex sets differ. -/
theorem Tet.exists_distinct_complement_vertices
    (τ ρ : Tet)
    (hτ : τ.verts.Nodup)
    (hρ : ρ.verts.Nodup)
    {a b c : Nat}
    (habc : [a, b, c].Nodup)
    (haτ : a ∈ τ.verts)
    (hbτ : b ∈ τ.verts)
    (hcτ : c ∈ τ.verts)
    (haρ : a ∈ ρ.verts)
    (hbρ : b ∈ ρ.verts)
    (hcρ : c ∈ ρ.verts)
    (hne : ¬ SameTetVertices τ ρ) :
    ∃ d e,
      d ∈ τ.verts ∧
      d ∉ [a, b, c] ∧
      e ∈ ρ.verts ∧
      e ∉ [a, b, c] ∧
      d ≠ e ∧
      (∀ v ∈ τ.verts, v = a ∨ v = b ∨ v = c ∨ v = d) ∧
      (∀ v ∈ ρ.verts, v = a ∨ v = b ∨ v = c ∨ v = e) := by
  obtain ⟨d, hd, hdUnique⟩ :=
    τ.exists_unique_complement_vertex hτ habc haτ hbτ hcτ
  obtain ⟨e, he, heUnique⟩ :=
    ρ.exists_unique_complement_vertex hρ habc haρ hbρ hcρ
  have hτCover :
      ∀ v ∈ τ.verts, v = a ∨ v = b ∨ v = c ∨ v = d := by
    intro v hv
    by_cases hvabc : v ∈ [a, b, c]
    · simp at hvabc
      rcases hvabc with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · right
      right
      right
      apply hdUnique v
      simpa using And.intro hv hvabc
  have hρCover :
      ∀ v ∈ ρ.verts, v = a ∨ v = b ∨ v = c ∨ v = e := by
    intro v hv
    by_cases hvabc : v ∈ [a, b, c]
    · simp at hvabc
      rcases hvabc with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · right
      right
      right
      apply heUnique v
      simpa using And.intro hv hvabc
  have hde : d ≠ e := by
    intro h
    apply hne
    intro v
    constructor
    · intro hv
      rcases hτCover v hv with rfl | rfl | rfl | rfl
      · exact haρ
      · exact hbρ
      · exact hcρ
      · simpa [h] using he.1
    · intro hv
      rcases hρCover v hv with rfl | rfl | rfl | rfl
      · exact haτ
      · exact hbτ
      · exact hcτ
      · simpa [h] using hd.1
  exact ⟨d, e, hd.1, by simpa using hd.2, he.1, by simpa using he.2,
    hde, hτCover, hρCover⟩

end Poincare
