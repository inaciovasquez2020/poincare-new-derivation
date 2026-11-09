import Poincare.Triangulation


/-!
Proof candidate at the genuine Tet/Triangulation interface, without Moves or geometry.
`SameTetSupport` has exactly the defining body of Moves.SameTetVertices,
so the hypotheses may later be discharged with actual `Move32Site.RealizedIn`.
This file is NOT claimed Lean-verified until run with the pinned Mac toolchain.
-/

namespace Poincare
namespace SecondRimOrderInvariantCore

/-- The defining formula of `SameTetVertices`, isolated to avoid importing Moves. -/
def SameTetSupport (τ σ : Tet) : Prop :=
  ∀ v : Nat, v ∈ τ.verts ↔ v ∈ σ.verts

/-- Order-invariant version of the old-face obstruction for a realized second site.
The target tetrahedra need not have a particular field order. -/
theorem secondSourceTripleAvoidsOldB
    (K₂ : Triangulation)
    (a b c p q r : Nat)
    (hOld : ∀ τ ∈ K₂.tets,
      ¬ (a ∈ τ.verts ∧ b ∈ τ.verts ∧ c ∈ τ.verts))
    (hTarget₀ : ∃ τ ∈ K₂.tets,
      SameTetSupport τ (⟨p,q,a,c⟩ : Tet))
    (hTarget₁ : ∃ τ ∈ K₂.tets,
      SameTetSupport τ (⟨p,r,a,c⟩ : Tet)) :
    b ∉ [p,q,r] := by
  obtain ⟨τ₀, hτ₀, hsame₀⟩ := hTarget₀
  obtain ⟨τ₁, hτ₁, hsame₁⟩ := hTarget₁
  have hnot₀ : b ∉ τ₀.verts := by
    intro hb
    exact hOld τ₀ hτ₀
      ⟨(hsame₀ a).2 (by simp [Tet.verts]),
       hb,
       (hsame₀ c).2 (by simp [Tet.verts])⟩
  have hnot₁ : b ∉ τ₁.verts := by
    intro hb
    exact hOld τ₁ hτ₁
      ⟨(hsame₁ a).2 (by simp [Tet.verts]),
       hb,
       (hsame₁ c).2 (by simp [Tet.verts])⟩
  intro hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hbp | hbq | hbr
  · exact hnot₀ ((hsame₀ b).2 (by simp [Tet.verts, hbp]))
  · exact hnot₀ ((hsame₀ b).2 (by simp [Tet.verts, hbq]))
  · exact hnot₁ ((hsame₁ b).2 (by simp [Tet.verts, hbr]))

/-- The remaining source-face vertex is outside all five original labels,
conditional only on the separately supplied distinctness facts. -/
theorem secondTransverseOutsideOriginalFive
    (K₂ : Triangulation)
    (a b c d e p q r y : Nat)
    (hOld : ∀ τ ∈ K₂.tets,
      ¬ (a ∈ τ.verts ∧ b ∈ τ.verts ∧ c ∈ τ.verts))
    (hTarget₀ : ∃ τ ∈ K₂.tets,
      SameTetSupport τ (⟨p,q,a,c⟩ : Tet))
    (hTarget₁ : ∃ τ ∈ K₂.tets,
      SameTetSupport τ (⟨p,r,a,c⟩ : Tet))
    (hy : y ∈ [p,q,r])
    (hya : y ≠ a) (hyc : y ≠ c)
    (hyd : y ≠ d) (hye : y ≠ e) :
    y ∉ [a,b,c,d,e] := by
  have hnotB := secondSourceTripleAvoidsOldB
    K₂ a b c p q r hOld hTarget₀ hTarget₁
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with ha | hb | hc | hd | he
  · exact hya ha
  · exact hnotB (hb ▸ hy)
  · exact hyc hc
  · exact hyd hd
  · exact hye he

end SecondRimOrderInvariantCore
end Poincare

#check Poincare.SecondRimOrderInvariantCore.secondSourceTripleAvoidsOldB
#check Poincare.SecondRimOrderInvariantCore.secondTransverseOutsideOriginalFive
#print axioms Poincare.SecondRimOrderInvariantCore.secondSourceTripleAvoidsOldB
#print axioms Poincare.SecondRimOrderInvariantCore.secondTransverseOutsideOriginalFive


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

namespace Poincare
namespace SecondRimComposedFreshness

theorem secondSourceFaceAbsent_of_realizedTargets_and_prefix
    (K K₂ : Triangulation) (R₂₃ R₃₂ : List Tet)
    (a b c d e z y p q r : Nat)
    (hOld : ∀ τ ∈ K₂.tets,
      ¬ (a ∈ τ.verts ∧ b ∈ τ.verts ∧ c ∈ τ.verts))
    (hTarget₀ : ∃ τ ∈ K₂.tets,
      SecondRimOrderInvariantCore.SameTetSupport τ (⟨p,q,a,c⟩ : Tet))
    (hTarget₁ : ∃ τ ∈ K₂.tets,
      SecondRimOrderInvariantCore.SameTetSupport τ (⟨p,r,a,c⟩ : Tet))
    (hy : y ∈ [p,q,r])
    (hya : y ≠ a) (hyc : y ≠ c)
    (hyd : y ≠ d) (hye : y ≠ e)
    (hNewEdgeAbsent : ∀ τ ∈ K.tets,
      ¬ (d ∈ τ.verts ∧ e ∈ τ.verts))
    (hRet₂₃ : ∀ τ ∈ R₂₃, τ ∈ K.tets)
    (hRet₃₂ : ∀ τ ∈ R₃₂,
      τ ∈ (⟨a,b,d,e⟩ : Tet) :: (⟨a,c,d,e⟩ : Tet) ::
        (⟨b,c,d,e⟩ : Tet) :: R₂₃)
    (hPrefix : K₂.tets =
      (⟨d,e,z,a⟩ : Tet) :: (⟨d,e,z,b⟩ : Tet) :: R₃₂)
    (hSeparated : y ≠ z) :
    ∀ τ ∈ K₂.tets,
      ¬ (d ∈ τ.verts ∧ e ∈ τ.verts ∧ y ∈ τ.verts) := by
  have hFresh : y ∉ [a,b,c,d,e] :=
    SecondRimOrderInvariantCore.secondTransverseOutsideOriginalFive
      K₂ a b c d e p q r y hOld hTarget₀ hTarget₁
      hy hya hyc hyd hye
  exact SecondRimActualTetTransport.sourceFaceAbsentAfterConcretePrefix
    K K₂ R₂₃ R₃₂ a b c d e z y hNewEdgeAbsent
    hRet₂₃ hRet₃₂ hPrefix hFresh hSeparated

end SecondRimComposedFreshness
end Poincare

#print axioms Poincare.SecondRimComposedFreshness.secondSourceFaceAbsent_of_realizedTargets_and_prefix
