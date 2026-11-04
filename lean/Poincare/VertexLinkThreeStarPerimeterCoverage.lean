import Poincare.VertexLinkThreeStarPerimeterEdgeSet
import Poincare.GlobalMove32IncidenceThreeCandidate
import Mathlib.Tactic

namespace Poincare

/--
Every perimeter edge of the complete incidence-three vertex-link star
is one of the three pairwise distinct opposite edges furnished by the
existing exact-three support normal form.
-/
theorem ClosedTriangulationCore.incidenceThree_star_perimeterEdgeSet_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hthree :
      (K.tets.filter
        (fun τ => v ∈ τ.verts ∧ x ∈ τ.verts)).length = 3) :
    ∃ a b c : Nat, ∃ hab : a ≠ b, ∃ hac : a ≠ c, ∃ hbc : b ≠ c,
      {f : LinkEdge |
        (∃ σ ∈ vertexLinkStarTriangles K v x, f.InTriangle σ) ∧
          ¬(x = f.lo ∨ x = f.hi)} =
      {LinkEdge.ofDistinct a b hab,
       LinkEdge.ofDistinct a c hac,
       LinkEdge.ofDistinct b c hbc} := by
  classical
  obtain ⟨σ₀, σ₁, σ₂, a, b, c,
    hσ₀, hσ₁, hσ₂, hax, hbx, hcx,
    hab, hac, hbc, hsup₀, hsup₁, hsup₂⟩ :=
    hcore.exists_incidenceThree_vertexLink_support_normalForm v x hvx hthree

  have hx₀ : x ∈ σ₀.verts := (hsup₀ x).2 (Or.inl rfl)
  have hx₁ : x ∈ σ₁.verts := (hsup₁ x).2 (Or.inl rfl)
  have hx₂ : x ∈ σ₂.verts := (hsup₂ x).2 (Or.inl rfl)

  have hs₀ : σ₀ ∈ vertexLinkStarTriangles K v x :=
    (mem_vertexLinkStarTriangles_iff K v x σ₀).2 ⟨hσ₀, hx₀⟩
  have hs₁ : σ₁ ∈ vertexLinkStarTriangles K v x :=
    (mem_vertexLinkStarTriangles_iff K v x σ₁).2 ⟨hσ₁, hx₁⟩
  have hs₂ : σ₂ ∈ vertexLinkStarTriangles K v x :=
    (mem_vertexLinkStarTriangles_iff K v x σ₂).2 ⟨hσ₂, hx₂⟩

  have h01 : σ₀ ≠ σ₁ := by
    intro heq
    have hb₀ : b ∈ σ₀.verts :=
      (hsup₀ b).2 (Or.inr (Or.inr rfl))
    have hb₁ : b ∈ σ₁.verts := heq ▸ hb₀
    rcases (hsup₁ b).1 hb₁ with h | h | h
    · exact hbx h
    · exact hab h.symm
    · exact hbc h

  have h02 : σ₀ ≠ σ₂ := by
    intro heq
    have ha₀ : a ∈ σ₀.verts :=
      (hsup₀ a).2 (Or.inr (Or.inl rfl))
    have ha₂ : a ∈ σ₂.verts := heq ▸ ha₀
    rcases (hsup₂ a).1 ha₂ with h | h | h
    · exact hax h
    · exact hab h
    · exact hac h

  have h12 : σ₁ ≠ σ₂ := by
    intro heq
    have ha₁ : a ∈ σ₁.verts :=
      (hsup₁ a).2 (Or.inr (Or.inl rfl))
    have ha₂ : a ∈ σ₂.verts := heq ▸ ha₁
    rcases (hsup₂ a).1 ha₂ with h | h | h
    · exact hax h
    · exact hab h
    · exact hac h

  have hlen :
      (vertexLinkStarTriangles K v x).length = 3 :=
    hcore.vertexLinkStarTriangles_length_eq_three_of_edgeIncidence_three
      v x hvx hthree

  have hnodup : (vertexLinkStarTriangles K v x).Nodup := by
    unfold vertexLinkStarTriangles
    exact (vertexLinkTriangles_nodup K hcore v).filter _

  have hstarCard :
      (vertexLinkStarTriangles K v x).toFinset.card = 3 := by
    rw [List.toFinset_card_of_nodup hnodup]
    exact hlen

  have htripleCard :
      ({σ₀, σ₁, σ₂} : Finset LinkTriangle).card = 3 := by
    simp [h01, h02, h12]

  have hsubset :
      ({σ₀, σ₁, σ₂} : Finset LinkTriangle) ⊆
        (vertexLinkStarTriangles K v x).toFinset := by
    intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl | rfl
    · exact List.mem_toFinset.mpr hs₀
    · exact List.mem_toFinset.mpr hs₁
    · exact List.mem_toFinset.mpr hs₂

  have hstarEq :
      ({σ₀, σ₁, σ₂} : Finset LinkTriangle) =
        (vertexLinkStarTriangles K v x).toFinset := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hstarCard, htripleCard]

  have hcover (σ : LinkTriangle) :
      σ ∈ vertexLinkStarTriangles K v x ↔
        σ = σ₀ ∨ σ = σ₁ ∨ σ = σ₂ := by
    constructor
    · intro hσ
      have hh : σ ∈ ({σ₀, σ₁, σ₂} : Finset LinkTriangle) := by
        rw [hstarEq]
        exact List.mem_toFinset.mpr hσ
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    · intro hσ
      have hh : σ ∈ ({σ₀, σ₁, σ₂} : Finset LinkTriangle) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hσ
      rw [hstarEq] at hh
      exact List.mem_toFinset.mp hh

  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  calc
    {f : LinkEdge |
      (∃ σ ∈ vertexLinkStarTriangles K v x, f.InTriangle σ) ∧
        ¬(x = f.lo ∨ x = f.hi)} =
      {f : LinkEdge |
        (f.InTriangle σ₀ ∨ f.InTriangle σ₁ ∨ f.InTriangle σ₂) ∧
          ¬(x = f.lo ∨ x = f.hi)} := by
            ext f
            constructor
            · rintro ⟨⟨σ, hσ, he⟩, hn⟩
              rcases (hcover σ).1 hσ with h | h | h
              · subst σ
                exact ⟨Or.inl he, hn⟩
              · subst σ
                exact ⟨Or.inr (Or.inl he), hn⟩
              · subst σ
                exact ⟨Or.inr (Or.inr he), hn⟩
            · rintro ⟨h, hn⟩
              rcases h with h | h | h
              · exact ⟨⟨σ₀, hs₀, h⟩, hn⟩
              · exact ⟨⟨σ₁, hs₁, h⟩, hn⟩
              · exact ⟨⟨σ₂, hs₂, h⟩, hn⟩
    _ = {LinkEdge.ofDistinct a b hab,
         LinkEdge.ofDistinct a c hac,
         LinkEdge.ofDistinct b c hbc} :=
      threeTriangleNormalForm_perimeterEdgeSet_eq
        σ₀ σ₁ σ₂ x a b c hax hbx hcx
        hab hac hbc hsup₀ hsup₁ hsup₂

end Poincare
