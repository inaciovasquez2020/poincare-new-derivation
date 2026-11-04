import Poincare.VertexLinkMod2Chain
import Mathlib.Tactic

namespace Poincare

/--
The three normal-form triangles with supports {x,a,b}, {x,a,c},
{x,b,c} have exactly the perimeter-edge set {ab,ac,bc}.

The support hypotheses are supplied independently by
ClosedTriangulationCore.exists_incidenceThree_vertexLink_support_normalForm.
This statement does not assume the sought perimeter-edge equality.
-/
theorem threeTriangleNormalForm_perimeterEdgeSet_eq
    (σ₀ σ₁ σ₂ : LinkTriangle)
    (x a b c : Nat)
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsup₀ :
      ∀ q : Nat, q ∈ σ₀.verts ↔ q = x ∨ q = a ∨ q = b)
    (hsup₁ :
      ∀ q : Nat, q ∈ σ₁.verts ↔ q = x ∨ q = a ∨ q = c)
    (hsup₂ :
      ∀ q : Nat, q ∈ σ₂.verts ↔ q = x ∨ q = b ∨ q = c) :
    {f : LinkEdge |
      (f.InTriangle σ₀ ∨ f.InTriangle σ₁ ∨ f.InTriangle σ₂) ∧
        ¬(x = f.lo ∨ x = f.hi)} =
      {LinkEdge.ofDistinct a b hab,
       LinkEdge.ofDistinct a c hac,
       LinkEdge.ofDistinct b c hbc} := by
  classical
  have unique (σ : LinkTriangle) (u w : Nat)
      (hxu : x ≠ u) (hxw : x ≠ w) (huw : u ≠ w)
      (hsupp : ∀ q : Nat, q ∈ σ.verts ↔ q = x ∨ q = u ∨ q = w)
      (f : LinkEdge) :
      (f.InTriangle σ ∧ ¬(x = f.lo ∨ x = f.hi)) ↔
        f = LinkEdge.ofDistinct u w huw := by
    constructor
    · rintro ⟨he, hnot⟩
      have hlo : f.lo = u ∨ f.lo = w := by
        rcases (hsupp f.lo).1 he.1 with hx | hu | hw
        · exact (hnot (Or.inl hx.symm)).elim
        · exact Or.inl hu
        · exact Or.inr hw
      have hhi : f.hi = u ∨ f.hi = w := by
        rcases (hsupp f.hi).1 he.2 with hx | hu | hw
        · exact (hnot (Or.inr hx.symm)).elim
        · exact Or.inl hu
        · exact Or.inr hw
      rcases f with ⟨lo, hi, hlt⟩
      change lo = u ∨ lo = w at hlo
      change hi = u ∨ hi = w at hhi
      rcases hlo with hlo | hlo
      · rcases hhi with hhi | hhi
        · omega
        · subst lo
          subst hi
          simp [LinkEdge.ofDistinct, hlt]
      · rcases hhi with hhi | hhi
        · subst lo
          subst hi
          have hnotlt : ¬ u < w := by omega
          simp [LinkEdge.ofDistinct, hnotlt]
        · omega
    · intro hf
      subst f
      constructor
      · exact LinkEdge.ofDistinct_inTriangle σ u w huw
          ((hsupp u).2 (Or.inr (Or.inl rfl)))
          ((hsupp w).2 (Or.inr (Or.inr rfl)))
      · intro hx
        rcases (LinkEdge.incident_ofDistinct_iff u w x huw).1 hx with hu | hw
        · exact hxu hu
        · exact hxw hw
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨htri, hn⟩
    rcases htri with h₀ | h₁ | h₂
    · exact Or.inl
        ((unique σ₀ a b hax.symm hbx.symm hab hsup₀ f).1 ⟨h₀, hn⟩)
    · exact Or.inr (Or.inl
        ((unique σ₁ a c hax.symm hcx.symm hac hsup₁ f).1 ⟨h₁, hn⟩))
    · exact Or.inr (Or.inr
        ((unique σ₂ b c hbx.symm hcx.symm hbc hsup₂ f).1 ⟨h₂, hn⟩))
  · intro hf
    rcases hf with h₀ | h₁ | h₂
    · obtain ⟨he, hn⟩ :=
        (unique σ₀ a b hax.symm hbx.symm hab hsup₀ f).2 h₀
      exact ⟨Or.inl he, hn⟩
    · obtain ⟨he, hn⟩ :=
        (unique σ₁ a c hax.symm hcx.symm hac hsup₁ f).2 h₁
      exact ⟨Or.inr (Or.inl he), hn⟩
    · obtain ⟨he, hn⟩ :=
        (unique σ₂ b c hbx.symm hcx.symm hbc hsup₂ f).2 h₂
      exact ⟨Or.inr (Or.inr he), hn⟩

end Poincare
