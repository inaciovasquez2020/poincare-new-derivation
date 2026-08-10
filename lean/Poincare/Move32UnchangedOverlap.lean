import Poincare.Move32SurvivorClassification

open Set

namespace Poincare

theorem ClosedTriangulationCore.move32Site_unchangedTet_inter_target_subset_source
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    triangulationTopologicalTetBody tau ∩
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiSourceLocalCarrier s.a s.b s.c s.d s.e := by
  obtain ⟨rho0, rho1, rho2, h0, h1, h2, hs0, hs1, hs2, hregion⟩ :=
    s.exists_actual_target_region hlegal.1
  have hm := hcore.move32Site_survivor s hlegal htau
  have hedge := hcore.move32Site_unchangedTet_not_contains_sharedEdge s hlegal htau
  intro p hp
  rw [← hregion] at hp
  rcases hp with ⟨hpTau, (hp0 | hp1) | hp2⟩
  all_goals
    have hmissing : s.d ∉ tau.verts ∨ s.e ∉ tau.verts := by
      by_cases hd : s.d ∈ tau.verts
      · exact Or.inr (fun he => hedge ⟨hd, he⟩)
      · exact Or.inl hd
  · rcases hmissing with hd | he
    · apply Or.inr
      simpa using tetBody_inter_subset_of_common_support K tau rho0 s.sourceTet₁
        hm.1 h0 (common_support_subset_of_missing tau rho0 s.sourceTet₁ s.d hd
          (by intro v hv; have hv' := (hs0 v).1 hv
              simp [Move32Site.targetTet₀, Move32Site.sourceTet₁, Tet.verts] at hv' ⊢
              aesop)) ⟨hpTau, hp0⟩
    · apply Or.inl
      simpa using tetBody_inter_subset_of_common_support K tau rho0 s.sourceTet₀
        hm.1 h0 (common_support_subset_of_missing tau rho0 s.sourceTet₀ s.e he
          (by intro v hv; have hv' := (hs0 v).1 hv
              simp [Move32Site.targetTet₀, Move32Site.sourceTet₀, Tet.verts] at hv' ⊢
              aesop)) ⟨hpTau, hp0⟩
  · rcases hmissing with hd | he
    · apply Or.inr
      simpa using tetBody_inter_subset_of_common_support K tau rho1 s.sourceTet₁
        hm.1 h1 (common_support_subset_of_missing tau rho1 s.sourceTet₁ s.d hd
          (by intro v hv; have hv' := (hs1 v).1 hv
              simp [Move32Site.targetTet₁, Move32Site.sourceTet₁, Tet.verts] at hv' ⊢
              aesop)) ⟨hpTau, hp1⟩
    · apply Or.inl
      simpa using tetBody_inter_subset_of_common_support K tau rho1 s.sourceTet₀
        hm.1 h1 (common_support_subset_of_missing tau rho1 s.sourceTet₀ s.e he
          (by intro v hv; have hv' := (hs1 v).1 hv
              simp [Move32Site.targetTet₁, Move32Site.sourceTet₀, Tet.verts] at hv' ⊢
              aesop)) ⟨hpTau, hp1⟩
  · rcases hmissing with hd | he
    · apply Or.inr
      simpa using tetBody_inter_subset_of_common_support K tau rho2 s.sourceTet₁
        hm.1 h2 (common_support_subset_of_missing tau rho2 s.sourceTet₁ s.d hd
          (by intro v hv; have hv' := (hs2 v).1 hv
              simp [Move32Site.targetTet₂, Move32Site.sourceTet₁, Tet.verts] at hv' ⊢
              aesop)) ⟨hpTau, hp2⟩
    · apply Or.inl
      simpa using tetBody_inter_subset_of_common_support K tau rho2 s.sourceTet₀
        hm.1 h2 (common_support_subset_of_missing tau rho2 s.sourceTet₀ s.e he
          (by intro v hv; have hv' := (hs2 v).1 hv
              simp [Move32Site.targetTet₂, Move32Site.sourceTet₀, Tet.verts] at hv' ⊢
              aesop)) ⟨hpTau, hp2⟩

theorem ClosedTriangulationCore.move32Site_unchangedTet_inter_source_subset_target
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    triangulationTopologicalTetBody tau ∩
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  have hm := hcore.move32Site_survivor s hlegal htau
  have hface := hcore.move32Site_unchangedTet_not_contains_sourceFace s hlegal htau
  rcases s.sourceTets_mem_replace K with ⟨h0, h1⟩
  intro p hp
  rcases hp with ⟨hpTau, hp0 | hp1⟩
  all_goals
    have hmissing : s.a ∉ tau.verts ∨ s.b ∉ tau.verts ∨ s.c ∉ tau.verts := by
      by_cases ha : s.a ∈ tau.verts
      · by_cases hb : s.b ∈ tau.verts
        · exact Or.inr (Or.inr (fun hc => hface ⟨ha, hb, hc⟩))
        · exact Or.inr (Or.inl hb)
      · exact Or.inl ha
  · rcases hmissing with ha | hb | hc
    · apply Or.inr
      simpa using (tetBody_inter_subset_of_common_support (s.replace K) tau s.sourceTet₀
        s.targetTet₂ hm.2.1 h0 (common_support_subset_of_missing tau s.sourceTet₀
          s.targetTet₂ s.a ha (by intro v hv; simp [Move32Site.sourceTet₀,
            Move32Site.targetTet₂, Tet.verts] at hv ⊢; aesop)) ⟨hpTau, by simpa using hp0⟩)
    · apply Or.inl; apply Or.inr
      simpa using (tetBody_inter_subset_of_common_support (s.replace K) tau
        s.sourceTet₀ s.targetTet₁ hm.2.1 h0 (common_support_subset_of_missing tau
          s.sourceTet₀ s.targetTet₁ s.b hb (by intro v hv; simp [Move32Site.sourceTet₀,
            Move32Site.targetTet₁, Tet.verts] at hv ⊢; aesop)) ⟨hpTau, by simpa using hp0⟩)
    · apply Or.inl; apply Or.inl
      simpa using (tetBody_inter_subset_of_common_support (s.replace K) tau
        s.sourceTet₀ s.targetTet₀ hm.2.1 h0 (common_support_subset_of_missing tau
          s.sourceTet₀ s.targetTet₀ s.c hc (by intro v hv; simp [Move32Site.sourceTet₀,
            Move32Site.targetTet₀, Tet.verts] at hv ⊢; aesop)) ⟨hpTau, by simpa using hp0⟩)
  · rcases hmissing with ha | hb | hc
    · apply Or.inr
      simpa using (tetBody_inter_subset_of_common_support (s.replace K) tau s.sourceTet₁
        s.targetTet₂ hm.2.1 h1 (common_support_subset_of_missing tau s.sourceTet₁
          s.targetTet₂ s.a ha (by intro v hv; simp [Move32Site.sourceTet₁,
            Move32Site.targetTet₂, Tet.verts] at hv ⊢; aesop)) ⟨hpTau, by simpa using hp1⟩)
    · apply Or.inl; apply Or.inr
      simpa using (tetBody_inter_subset_of_common_support (s.replace K) tau
        s.sourceTet₁ s.targetTet₁ hm.2.1 h1 (common_support_subset_of_missing tau
          s.sourceTet₁ s.targetTet₁ s.b hb (by intro v hv; simp [Move32Site.sourceTet₁,
            Move32Site.targetTet₁, Tet.verts] at hv ⊢; aesop)) ⟨hpTau, by simpa using hp1⟩)
    · apply Or.inl; apply Or.inl
      simpa using (tetBody_inter_subset_of_common_support (s.replace K) tau
        s.sourceTet₁ s.targetTet₀ hm.2.1 h1 (common_support_subset_of_missing tau
          s.sourceTet₁ s.targetTet₀ s.c hc (by intro v hv; simp [Move32Site.sourceTet₁,
            Move32Site.targetTet₀, Tet.verts] at hv ⊢; aesop)) ⟨hpTau, by simpa using hp1⟩)

theorem ClosedTriangulationCore.move32Site_unchangedCarrier_inter_target_subset_source
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    s.unchangedGeometricCarrier K ∩ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiSourceLocalCarrier s.a s.b s.c s.d s.e := by
  rintro p ⟨hpU, hpT⟩
  simp only [Move32Site.unchangedGeometricCarrier, mem_iUnion] at hpU
  obtain ⟨tau, htau, hpTau⟩ := hpU
  exact hcore.move32Site_unchangedTet_inter_target_subset_source s hlegal htau ⟨hpTau, hpT⟩

theorem ClosedTriangulationCore.move32Site_unchangedCarrier_inter_source_subset_target
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    s.unchangedGeometricCarrier K ∩ move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  rintro p ⟨hpU, hpS⟩
  simp only [Move32Site.unchangedGeometricCarrier, mem_iUnion] at hpU
  obtain ⟨tau, htau, hpTau⟩ := hpU
  exact hcore.move32Site_unchangedTet_inter_source_subset_target s hlegal htau ⟨hpTau, hpS⟩

theorem ClosedTriangulationCore.move32LocalInverse_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (q : ↥(move23PiTargetLocalCarrier s.a s.b s.c s.d s.e))
    (hqU : q.1 ∈ s.unchangedGeometricCarrier K) :
    ((move23PiLocalHomeomorph (hcore.move32Site_distinct s hlegal.1)).symm q).1 = q.1 := by
  have hfive := hcore.move32Site_distinct s hlegal.1
  apply move23PiLocalHomeomorph_symm_apply_eq_of_mem_source hfive q
  exact hcore.move32Site_unchangedCarrier_inter_target_subset_source s hlegal ⟨hqU, q.2⟩

theorem ClosedTriangulationCore.move32LocalForward_apply_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (p : ↥(move23PiSourceLocalCarrier s.a s.b s.c s.d s.e))
    (hpU : p.1 ∈ s.unchangedGeometricCarrier K) :
    (move23PiLocalHomeomorph (hcore.move32Site_distinct s hlegal.1) p).1 = p.1 := by
  have hfive := hcore.move32Site_distinct s hlegal.1
  apply move23PiLocalHomeomorph_apply_eq_of_mem_target hfive p
  exact hcore.move32Site_unchangedCarrier_inter_source_subset_target s hlegal ⟨hpU, p.2⟩

theorem ClosedTriangulationCore.move32Site_overlap_compatibility
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K) :
    (s.unchangedGeometricCarrier K ∩ move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e) ∧
      (s.unchangedGeometricCarrier K ∩ move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e) :=
  ⟨hcore.move32Site_unchangedCarrier_inter_target_subset_source s hlegal,
    hcore.move32Site_unchangedCarrier_inter_source_subset_target s hlegal⟩

end Poincare
