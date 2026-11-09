import Poincare.Triangulation

/-!
Order-insensitive second-source-face exclusion in the actual Tet representation.
Retained membership hypotheses are precisely what the Moves eraseFirstSameTet
lemmas must provide upon later integration. Source-face freshness must be
supplied from the site geometry; it is NOT silently assumed as a consequence
of edge incidence alone.
-/

namespace Poincare
namespace SecondRimActualTetTransport

/-- Given the actual lists of inserted tetrahedra, retained-part membership,
no original d-e edge, and a fresh transverse y, the second d-e-y face is absent.
The new lists are the concrete 2-to-3 and first 3-to-2 insertions. -/
theorem sourceFaceAbsentAfterConcretePrefix
    (K K₂ : Triangulation)
    (R₂₃ R₃₂ : List Tet)
    (a b c d e z y : Nat)
    (hNewEdgeAbsent : ∀ τ ∈ K.tets,
      ¬ (d ∈ τ.verts ∧ e ∈ τ.verts))
    (hRet₂₃ : ∀ τ ∈ R₂₃, τ ∈ K.tets)
    (hRet₃₂ : ∀ τ ∈ R₃₂,
      τ ∈ (⟨a,b,d,e⟩ : Tet) :: (⟨a,c,d,e⟩ : Tet) ::
        (⟨b,c,d,e⟩ : Tet) :: R₂₃)
    (hPrefix : K₂.tets =
      (⟨d,e,z,a⟩ : Tet) :: (⟨d,e,z,b⟩ : Tet) :: R₃₂)
    (hFresh : y ∉ [a,b,c,d,e])
    (hSeparated : y ≠ z) :
    ∀ τ ∈ K₂.tets,
      ¬ (d ∈ τ.verts ∧ e ∈ τ.verts ∧ y ∈ τ.verts) := by
  have hya : y ≠ a := by
    intro h
    exact hFresh (by simp [h])
  have hyb : y ≠ b := by
    intro h
    exact hFresh (by simp [h])
  have hyc : y ≠ c := by
    intro h
    exact hFresh (by simp [h])
  have hyd : y ≠ d := by
    intro h
    exact hFresh (by simp [h])
  have hye : y ≠ e := by
    intro h
    exact hFresh (by simp [h])
  have h₀ : y ∉ (⟨d,e,z,a⟩ : Tet).verts := by
    simp [Tet.verts, hyd, hye, hSeparated, hya]
  have h₁ : y ∉ (⟨d,e,z,b⟩ : Tet).verts := by
    simp [Tet.verts, hyd, hye, hSeparated, hyb]
  have h₂ : y ∉ (⟨a,b,d,e⟩ : Tet).verts := by
    simp [Tet.verts, hya, hyb, hyd, hye]
  have h₃ : y ∉ (⟨a,c,d,e⟩ : Tet).verts := by
    simp [Tet.verts, hya, hyc, hyd, hye]
  have h₄ : y ∉ (⟨b,c,d,e⟩ : Tet).verts := by
    simp [Tet.verts, hyb, hyc, hyd, hye]
  intro τ hτ hface
  rw [hPrefix] at hτ
  rcases List.mem_cons.mp hτ with hτ₀ | hτmore
  · subst τ
    exact h₀ hface.2.2
  rcases List.mem_cons.mp hτmore with hτ₁ | hRet
  · subst τ
    exact h₁ hface.2.2
  have hPrevious := hRet₃₂ τ hRet
  rcases List.mem_cons.mp hPrevious with hτ₂ | hMore
  · subst τ
    exact h₂ hface.2.2
  rcases List.mem_cons.mp hMore with hτ₃ | hMore
  · subst τ
    exact h₃ hface.2.2
  rcases List.mem_cons.mp hMore with hτ₄ | hOld
  · subst τ
    exact h₄ hface.2.2
  exact hNewEdgeAbsent τ (hRet₂₃ τ hOld) ⟨hface.1, hface.2.1⟩

end SecondRimActualTetTransport
end Poincare

#check Poincare.SecondRimActualTetTransport.sourceFaceAbsentAfterConcretePrefix
#print axioms Poincare.SecondRimActualTetTransport.sourceFaceAbsentAfterConcretePrefix