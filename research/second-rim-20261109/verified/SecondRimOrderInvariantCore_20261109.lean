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