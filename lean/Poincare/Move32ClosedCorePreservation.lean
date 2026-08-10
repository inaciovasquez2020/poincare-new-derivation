import Poincare.Move32SurvivorClassification

namespace Poincare

/-- A legal `3-2` replacement preserves tetrahedron nondegeneracy and
vertex-set uniqueness. -/
theorem ClosedTriangulationCore.move32Site_replace_simple
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hlegal : s.LegalIn K) :
    (∀ tau ∈ (s.replace K).tets, tau.verts.Nodup) ∧
      (s.replace K).tets.Pairwise
        (fun tau sigma => ¬ SameTetVertices tau sigma) := by
  have hfive := hcore.move32Site_distinct s hlegal.1
  have hsource0 : s.sourceTet₀.verts.Nodup := by
    simp [Move32Site.sourceTet₀, Tet.verts] at ⊢
    simp at hfive
    aesop
  have hsource1 : s.sourceTet₁.verts.Nodup := by
    simp [Move32Site.sourceTet₁, Tet.verts] at ⊢
    simp at hfive
    aesop
  have hunchanged : ∀ tau ∈ s.unchangedTets K, tau.verts.Nodup := by
    intro tau htau
    exact hcore.1 tau (s.mem_original_of_mem_unchanged htau)
  have hsub : List.Sublist (s.unchangedTets K) K.tets := by
    exact (eraseFirstSameTet_sublist s.targetTet₂ _).trans
      ((eraseFirstSameTet_sublist s.targetTet₁ _).trans
        (eraseFirstSameTet_sublist s.targetTet₀ _))
  have hpair : (s.unchangedTets K).Pairwise
      (fun tau sigma => ¬ SameTetVertices tau sigma) :=
    hcore.2.1.sublist hsub
  have h01 : ¬ SameTetVertices s.sourceTet₀ s.sourceTet₁ := by
    intro hsame
    have hd : s.d ∈ s.sourceTet₁.verts :=
      (hsame s.d).1 (by simp [Move32Site.sourceTet₀, Tet.verts])
    simp [Move32Site.sourceTet₁, Tet.verts] at hd
    simp at hfive
    aesop
  have hsourceU : ∀ source ∈ [s.sourceTet₀, s.sourceTet₁],
      ∀ tau ∈ s.unchangedTets K, ¬ SameTetVertices source tau := by
    intro source hsource tau htau hsame
    apply hlegal.2.2 tau (s.mem_original_of_mem_unchanged htau)
    have ha : s.a ∈ source.verts := by
      rcases (by simpa using hsource : source = s.sourceTet₀ ∨
        source = s.sourceTet₁) with rfl | rfl <;>
        simp [Move32Site.sourceTet₀, Move32Site.sourceTet₁, Tet.verts]
    have hb : s.b ∈ source.verts := by
      rcases (by simpa using hsource : source = s.sourceTet₀ ∨
        source = s.sourceTet₁) with rfl | rfl <;>
        simp [Move32Site.sourceTet₀, Move32Site.sourceTet₁, Tet.verts]
    have hc : s.c ∈ source.verts := by
      rcases (by simpa using hsource : source = s.sourceTet₀ ∨
        source = s.sourceTet₁) with rfl | rfl <;>
        simp [Move32Site.sourceTet₀, Move32Site.sourceTet₁, Tet.verts]
    exact ⟨(hsame s.a).1 ha, (hsame s.b).1 hb, (hsame s.c).1 hc⟩
  constructor
  · intro tau htau
    rw [s.replace_tets_eq K] at htau
    simp only [List.mem_cons] at htau
    rcases htau with rfl | rfl | htau
    · exact hsource0
    · exact hsource1
    · exact hunchanged tau htau
  · rw [s.replace_tets_eq K]
    simp only [List.pairwise_cons, List.mem_cons]
    refine ⟨?_, ?_, hpair⟩
    · intro tau htau
      rcases htau with rfl | htau
      · exact h01
      · exact hsourceU s.sourceTet₀ (by simp) tau htau
    · exact fun tau htau => hsourceU s.sourceTet₁ (by simp) tau htau

end Poincare
