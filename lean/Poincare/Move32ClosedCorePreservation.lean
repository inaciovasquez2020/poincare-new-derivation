import Poincare.Move32SurvivorClassification
import Poincare.Move23FaceIncidenceTable

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

/-- Removing the three represented target tetrahedra splits every
vertex-set-invariant filtered count into its unchanged and local parts. -/
theorem ClosedTriangulationCore.move32Site_unchanged_filter_length_add_local_eq
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move32Site) (hlegal : s.LegalIn K)
    (p : Tet → Prop) [DecidablePred p]
    (hinvariant : ∀ τ σ, SameTetVertices τ σ → (p τ ↔ p σ)) :
    ((s.unchangedTets K).filter p).length +
        ([s.targetTet₀, s.targetTet₁, s.targetTet₂].filter p).length =
      (K.tets.filter p).length := by
  have hfive := hcore.move32Site_distinct s hlegal.1
  rcases hlegal.1 with ⟨h0, h1, h2⟩
  have hu0 := hcore.existsUnique_sameTetVertices h0
  have hu1 := hcore.existsUnique_sameTetVertices h1
  have hu2 := hcore.existsUnique_sameTetVertices h2
  have hu1' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu1
    (fun h => s.targetTet₀_not_same_targetTet₁ hfive (sameTetVertices_symm h))
  have hu2' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2
    (fun h => s.targetTet₀_not_same_targetTet₂ hfive (sameTetVertices_symm h))
  have hu2'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2'
    (fun h => s.targetTet₁_not_same_targetTet₂ hfive (sameTetVertices_symm h))
  by_cases hp0 : p s.targetTet₀
  · have e0 := eraseFirstSameTet_filter_length_add_one_eq
      p s.targetTet₀ K.tets hinvariant h0 hp0
    by_cases hp1 : p s.targetTet₁
    · have e1 := eraseFirstSameTet_filter_length_add_one_eq p s.targetTet₁
        (eraseFirstSameTet s.targetTet₀ K.tets) hinvariant
        ⟨hu1'.choose, hu1'.choose_spec.1.1, hu1'.choose_spec.1.2⟩ hp1
      by_cases hp2 : p s.targetTet₂
      · have e2 := eraseFirstSameTet_filter_length_add_one_eq p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant
          ⟨hu2''.choose, hu2''.choose_spec.1.1, hu2''.choose_spec.1.2⟩ hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega
      · have e2 := eraseFirstSameTet_filter_length_eq_of_not p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega
    · have e1 := eraseFirstSameTet_filter_length_eq_of_not p s.targetTet₁
        (eraseFirstSameTet s.targetTet₀ K.tets) hinvariant hp1
      by_cases hp2 : p s.targetTet₂
      · have e2 := eraseFirstSameTet_filter_length_add_one_eq p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant
          ⟨hu2''.choose, hu2''.choose_spec.1.1, hu2''.choose_spec.1.2⟩ hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega
      · have e2 := eraseFirstSameTet_filter_length_eq_of_not p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega
  · have e0 := eraseFirstSameTet_filter_length_eq_of_not
      p s.targetTet₀ K.tets hinvariant hp0
    by_cases hp1 : p s.targetTet₁
    · have e1 := eraseFirstSameTet_filter_length_add_one_eq p s.targetTet₁
        (eraseFirstSameTet s.targetTet₀ K.tets) hinvariant
        ⟨hu1'.choose, hu1'.choose_spec.1.1, hu1'.choose_spec.1.2⟩ hp1
      by_cases hp2 : p s.targetTet₂
      · have e2 := eraseFirstSameTet_filter_length_add_one_eq p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant
          ⟨hu2''.choose, hu2''.choose_spec.1.1, hu2''.choose_spec.1.2⟩ hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega
      · have e2 := eraseFirstSameTet_filter_length_eq_of_not p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega
    · have e1 := eraseFirstSameTet_filter_length_eq_of_not p s.targetTet₁
        (eraseFirstSameTet s.targetTet₀ K.tets) hinvariant hp1
      by_cases hp2 : p s.targetTet₂
      · have e2 := eraseFirstSameTet_filter_length_add_one_eq p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant
          ⟨hu2''.choose, hu2''.choose_spec.1.1, hu2''.choose_spec.1.2⟩ hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega
      · have e2 := eraseFirstSameTet_filter_length_eq_of_not p s.targetTet₂
          (eraseFirstSameTet s.targetTet₁
            (eraseFirstSameTet s.targetTet₀ K.tets)) hinvariant hp2
        simp [Move32Site.unchangedTets, hp0, hp1, hp2] at ⊢
        omega

/-- A legal `3-2` replacement preserves exact two-fold incidence of every
represented nondegenerate triangular face, and hence the full closed core. -/
theorem ClosedTriangulationCore.move32Site_replace_closedCore
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hlegal : s.LegalIn K) :
    ClosedTriangulationCore (s.replace K) := by
  refine ⟨(hcore.move32Site_replace_simple s hlegal).1,
    (hcore.move32Site_replace_simple s hlegal).2, ?_⟩
  intro x y z hxyz hrepresented
  let p : Tet → Prop := fun tau =>
    x ∈ tau.verts ∧ y ∈ tau.verts ∧ z ∈ tau.verts
  have hinvariant : ∀ tau sigma, SameTetVertices tau sigma →
      (p tau ↔ p sigma) := by
    intro tau sigma hsame
    simp only [p]
    constructor <;> intro h
    · exact ⟨(hsame x).1 h.1, (hsame y).1 h.2.1, (hsame z).1 h.2.2⟩
    · exact ⟨(hsame x).2 h.1, (hsame y).2 h.2.1, (hsame z).2 h.2.2⟩
  have hsplit := hcore.move32Site_unchanged_filter_length_add_local_eq
    s hlegal p hinvariant
  have hfilter (L : List Tet) :
      (L.filter p).length =
        (L.filter fun tau => tau.ContainsTriple x y z).length := by
    congr 2
    funext tau
    simp [p, Tet.ContainsTriple]
  have hreplace :
      ((s.replace K).tets.filter p).length =
        ([s.sourceTet₀, s.sourceTet₁].filter p).length +
          ((s.unchangedTets K).filter p).length := by
    change (([s.sourceTet₀, s.sourceTet₁] ++
      s.unchangedTets K).filter p).length = _
    rw [List.filter_append, List.length_append]
  change ((s.replace K).tets.filter p).length = 2
  have hfive := hcore.move32Site_distinct s hlegal.1
  let m := s.toMove23Site hfive
  have hKcount_of_target
      (hpos : 0 < ([s.targetTet₀, s.targetTet₁, s.targetTet₂].filter p).length) :
      (K.tets.filter p).length = 2 := by
    rcases List.length_pos_iff_exists_mem.mp hpos with ⟨rho, hrho⟩
    simp only [List.mem_filter] at hrho
    have hpRho : p rho := of_decide_eq_true hrho.2
    rcases (by simpa using hrho.1 : rho = s.targetTet₀ ∨
        rho = s.targetTet₁ ∨ rho = s.targetTet₂) with rfl | rfl | rfl
    · rcases hlegal.1.1 with ⟨tau, htau, hs⟩
      exact hcore.2.2 x y z hxyz
        ⟨tau, htau, (hinvariant tau s.targetTet₀ hs).2 hpRho⟩
    · rcases hlegal.1.2.1 with ⟨tau, htau, hs⟩
      exact hcore.2.2 x y z hxyz
        ⟨tau, htau, (hinvariant tau s.targetTet₁ hs).2 hpRho⟩
    · rcases hlegal.1.2.2 with ⟨tau, htau, hs⟩
      exact hcore.2.2 x y z hxyz
        ⟨tau, htau, (hinvariant tau s.targetTet₂ hs).2 hpRho⟩
  by_cases hsource : ∃ tau ∈ [s.sourceTet₀, s.sourceTet₁], p tau
  · rcases hsource with ⟨tau, htau, hp⟩
    have hcases := m.source_local_face_incidence_cases x y z hxyz (by simpa [m] using htau)
      ((Tet.containsTriple_eq_true tau x y z).2 hp)
    have closeBoundary
        (hb :
          SameTripleVertices x y z s.a s.b s.d ∨
          SameTripleVertices x y z s.a s.b s.e ∨
          SameTripleVertices x y z s.a s.c s.d ∨
          SameTripleVertices x y z s.a s.c s.e ∨
          SameTripleVertices x y z s.b s.c s.d ∨
          SameTripleVertices x y z s.b s.c s.e) :
        ((s.replace K).tets.filter p).length = 2 := by
      have hbal := m.boundaryFace_local_incidence_balance x y z (by simpa [m] using hb)
      change ([s.sourceTet₀, s.sourceTet₁].filter
          (fun rho => rho.ContainsTriple x y z)).length = 1 ∧
        ([s.targetTet₀, s.targetTet₁, s.targetTet₂].filter
          (fun rho => rho.ContainsTriple x y z)).length = 1 at hbal
      rw [← hfilter, ← hfilter] at hbal
      have hKcount := hKcount_of_target (by omega)
      omega
    rcases hcases with hb | hb | hb | hb | hb | hb | hi
    · exact closeBoundary (Or.inl (by simpa [m] using hb))
    · exact closeBoundary (Or.inr (Or.inl (by simpa [m] using hb)))
    · exact closeBoundary (Or.inr (Or.inr (Or.inl (by simpa [m] using hb))))
    · exact closeBoundary (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [m] using hb)))))
    · exact closeBoundary (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [m] using hb))))))
    · exact closeBoundary (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [m] using hb))))))
    · have hUzero : ((s.unchangedTets K).filter p).length = 0 := by
        apply List.length_eq_zero_iff.mpr
        apply List.filter_eq_nil_iff.mpr
        intro rho hrho hpDec
        have hpRho : p rho := of_decide_eq_true hpDec
        apply hlegal.2.2 rho (s.mem_original_of_mem_unchanged hrho)
        have habc := (by simpa [m] using hi : SameTripleVertices x y z s.a s.b s.c)
        have getMem (v : Nat) (hv : v = x ∨ v = y ∨ v = z) : v ∈ rho.verts := by
          rcases hv with rfl | rfl | rfl
          · exact hpRho.1
          · exact hpRho.2.1
          · exact hpRho.2.2
        exact ⟨getMem s.a ((habc s.a).2 (Or.inl rfl)),
          getMem s.b ((habc s.b).2 (Or.inr (Or.inl rfl))),
          getMem s.c ((habc s.c).2 (Or.inr (Or.inr rfl)))⟩
      have hlocal := m.local_internal_abc.1
      change ([s.sourceTet₀, s.sourceTet₁].filter
        (fun rho => rho.ContainsTriple s.a s.b s.c)).length = 2 at hlocal
      have hxlocal := filter_containsTriple_length_eq_of_sameTripleVertices
        [s.sourceTet₀, s.sourceTet₁] (by simpa [m] using hi)
      rw [← hfilter] at hxlocal
      have hpLocal : ([s.sourceTet₀, s.sourceTet₁].filter p).length = 2 :=
        hxlocal.trans hlocal
      omega
  · push Not at hsource
    have hsourceZero : ([s.sourceTet₀, s.sourceTet₁].filter p).length = 0 := by
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro rho hrho hpDec
      exact hsource rho hrho (of_decide_eq_true hpDec)
    rcases hrepresented with ⟨tau, htau, hp⟩
    rw [s.replace_tets_eq] at htau
    simp only [List.mem_cons] at htau
    rcases htau with rfl | rfl | htau
    · exact (hsource s.sourceTet₀ (by simp) hp).elim
    · exact (hsource s.sourceTet₁ (by simp) hp).elim
    · have htauK := s.mem_original_of_mem_unchanged htau
      have hKcount := hcore.2.2 x y z hxyz ⟨tau, htauK, hp⟩
      change (K.tets.filter p).length = 2 at hKcount
      have htargetZero :
          ([s.targetTet₀, s.targetTet₁, s.targetTet₂].filter p).length = 0 := by
        apply List.length_eq_zero_iff.mpr
        apply List.filter_eq_nil_iff.mpr
        intro rho hrho hpDec
        have hpRho : p rho := of_decide_eq_true hpDec
        have hcases := m.target_local_face_incidence_cases x y z hxyz
          (by simpa [m] using hrho) ((Tet.containsTriple_eq_true rho x y z).2 hpRho)
        have boundaryImpossible
            (hb :
              SameTripleVertices x y z s.a s.b s.d ∨
              SameTripleVertices x y z s.a s.b s.e ∨
              SameTripleVertices x y z s.a s.c s.d ∨
              SameTripleVertices x y z s.a s.c s.e ∨
              SameTripleVertices x y z s.b s.c s.d ∨
              SameTripleVertices x y z s.b s.c s.e) : False := by
          have hbal := m.boundaryFace_local_incidence_balance x y z
            (by simpa [m] using hb)
          change ([s.sourceTet₀, s.sourceTet₁].filter
              (fun q => q.ContainsTriple x y z)).length = 1 ∧ _ at hbal
          rw [← hfilter] at hbal
          omega
        have internalImpossible (u : Nat)
            (hi : SameTripleVertices x y z u s.d s.e) : False := by
          apply hcore.move32Site_unchangedTet_not_contains_sharedEdge s hlegal htau
          have getMem (v : Nat) (hv : v = x ∨ v = y ∨ v = z) : v ∈ tau.verts := by
            rcases hv with rfl | rfl | rfl
            · exact hp.1
            · exact hp.2.1
            · exact hp.2.2
          exact ⟨getMem s.d ((hi s.d).2 (Or.inr (Or.inl rfl))),
            getMem s.e ((hi s.e).2 (Or.inr (Or.inr rfl)))⟩
        rcases hcases with hb | hb | hb | hb | hb | hb | hi | hi | hi
        · exact boundaryImpossible (Or.inl (by simpa [m] using hb))
        · exact boundaryImpossible (Or.inr (Or.inl (by simpa [m] using hb)))
        · exact boundaryImpossible (Or.inr (Or.inr (Or.inl (by simpa [m] using hb))))
        · exact boundaryImpossible (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [m] using hb)))))
        · exact boundaryImpossible (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [m] using hb))))))
        · exact boundaryImpossible (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [m] using hb))))))
        · exact internalImpossible s.a (by simpa [m] using hi)
        · exact internalImpossible s.b (by simpa [m] using hi)
        · exact internalImpossible s.c (by simpa [m] using hi)
      have hUcount : ((s.unchangedTets K).filter p).length = 2 := by
        omega
      rw [hreplace]
      omega

end Poincare
