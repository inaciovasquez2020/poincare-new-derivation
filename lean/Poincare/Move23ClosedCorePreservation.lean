import Poincare.Move23FaceIncidenceTable
import Poincare.Move23UnchangedOverlap

namespace Poincare

/-- The `2-3` replacement preserves the two simplicial-complex parts of the
closed-core condition: every tetrahedron is nondegenerate and no two listed
tetrahedra have the same vertex set.  Face incidence is handled separately. -/
theorem ClosedTriangulationCore.move23Site_replace_simple
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    (hlegal : s.LegalIn K) :
    (∀ tau ∈ (s.replace K).tets, tau.verts.Nodup) ∧
      (s.replace K).tets.Pairwise
        (fun tau sigma => ¬ SameTetVertices tau sigma) := by
  have hdata := hcore.move23Site_simpleBistellarData s hlegal
  have hnew0 : s.newTet₀.verts.Nodup := hdata.2.2.2.2.2.1
  have hnew1 : s.newTet₁.verts.Nodup := hdata.2.2.2.2.2.2.1
  have hnew2 : s.newTet₂.verts.Nodup := hdata.2.2.2.2.2.2.2
  have hunchangedNodup :
      ∀ tau ∈ s.unchangedTets K, tau.verts.Nodup := by
    intro tau htau
    exact hcore.1 tau (hcore.move23Site_mem_unchangedTets s hlegal htau).1
  have hUsub : List.Sublist (s.unchangedTets K) K.tets := by
    exact (eraseFirstSameTet_sublist s.rightTet
      (eraseFirstSameTet s.leftTet K.tets)).trans
        (eraseFirstSameTet_sublist s.leftTet K.tets)
  have hUpair : (s.unchangedTets K).Pairwise
      (fun tau sigma => ¬ SameTetVertices tau sigma) :=
    hcore.2.1.sublist hUsub
  have hnew01 : ¬ SameTetVertices s.newTet₀ s.newTet₁ := by
    intro h
    have hb : s.b ∈ s.newTet₁.verts :=
      (h s.b).1 (by simp [Move23Site.newTet₀, Tet.verts])
    have hd := s.distinct
    simp [Move23Site.newTet₁, Tet.verts] at hb
    simp at hd
    aesop
  have hnew02 : ¬ SameTetVertices s.newTet₀ s.newTet₂ := by
    intro h
    have ha : s.a ∈ s.newTet₂.verts :=
      (h s.a).1 (by simp [Move23Site.newTet₀, Tet.verts])
    have hd := s.distinct
    simp [Move23Site.newTet₂, Tet.verts] at ha
    simp at hd
    aesop
  have hnew12 : ¬ SameTetVertices s.newTet₁ s.newTet₂ := by
    intro h
    have ha : s.a ∈ s.newTet₂.verts :=
      (h s.a).1 (by simp [Move23Site.newTet₁, Tet.verts])
    have hd := s.distinct
    simp [Move23Site.newTet₂, Tet.verts] at ha
    simp at hd
    aesop
  have hnewU : ∀ n ∈ [s.newTet₀, s.newTet₁, s.newTet₂],
      ∀ tau ∈ s.unchangedTets K, ¬ SameTetVertices n tau := by
    intro n hn tau htau hsame
    have htauK := (hcore.move23Site_mem_unchangedTets s hlegal htau).1
    apply hlegal.2.2 tau htauK
    constructor
    · exact (hsame s.d).1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;>
          simp [Move23Site.newTet₀, Move23Site.newTet₁,
            Move23Site.newTet₂, Tet.verts])
    · exact (hsame s.e).1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;>
          simp [Move23Site.newTet₀, Move23Site.newTet₁,
            Move23Site.newTet₂, Tet.verts])
  constructor
  · intro tau htau
    rw [s.replace_tets_eq K] at htau
    simp only [List.mem_cons] at htau
    rcases htau with rfl | rfl | rfl | htau
    · exact hnew0
    · exact hnew1
    · exact hnew2
    · exact hunchangedNodup tau htau
  · rw [s.replace_tets_eq K]
    simp only [List.pairwise_cons, List.mem_cons]
    refine ⟨?_, ?_, ?_, hUpair⟩
    · intro tau htau
      rcases htau with rfl | rfl | htau
      · exact hnew01
      · exact hnew02
      · exact hnewU s.newTet₀ (by simp) tau htau
    · intro tau htau
      rcases htau with rfl | htau
      · exact hnew12
      · exact hnewU s.newTet₁ (by simp) tau htau
    · exact fun tau htau => hnewU s.newTet₂ (by simp) tau htau

/-- A legal `2-3` bistellar replacement preserves the full closed
triangulation core, including exact two-fold incidence of every represented
nondegenerate triangular face. -/
theorem ClosedTriangulationCore.move23Site_replace_closedCore
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    (hlegal : s.LegalIn K) :
    ClosedTriangulationCore (s.replace K) := by
  refine ⟨(hcore.move23Site_replace_simple s hlegal).1,
    (hcore.move23Site_replace_simple s hlegal).2, ?_⟩
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
  have hsource := hcore.move23Site_unchanged_filter_length_add_local_eq
    s hlegal p hinvariant
  have hfilter (L : List Tet) :
      (L.filter p).length =
        (L.filter fun tau => tau.ContainsTriple x y z).length := by
    congr 2
    funext tau
    simp [p, Tet.ContainsTriple]
  have hreplace :
      ((s.replace K).tets.filter p).length =
        ([s.newTet₀, s.newTet₁, s.newTet₂].filter p).length +
          ((s.unchangedTets K).filter p).length := by
    change (([s.newTet₀, s.newTet₁, s.newTet₂] ++
      s.unchangedTets K).filter p).length = _
    rw [List.filter_append, List.length_append]
  change ((s.replace K).tets.filter p).length = 2
  have hKcount_of_source
      (hpos : 0 < ([s.leftTet, s.rightTet].filter p).length) :
      (K.tets.filter p).length = 2 := by
    rcases List.length_pos_iff_exists_mem.mp hpos with ⟨rho, hrho⟩
    simp only [List.mem_filter] at hrho
    have hpRho : p rho := of_decide_eq_true hrho.2
    rcases (by simpa using hrho.1 : rho = s.leftTet ∨ rho = s.rightTet) with rfl | rfl
    · have hdata := (hcore.move23Site_simpleBistellarData s hlegal).2.1.choose_spec.1
      exact hcore.2.2 x y z hxyz
        ⟨_, hdata.1, (hinvariant _ s.leftTet hdata.2).2 hpRho⟩
    · have hdata := (hcore.move23Site_simpleBistellarData s hlegal).2.2.1.choose_spec.1
      exact hcore.2.2 x y z hxyz
        ⟨_, hdata.1, (hinvariant _ s.rightTet hdata.2).2 hpRho⟩
  by_cases htarget : ∃ tau ∈ [s.newTet₀, s.newTet₁, s.newTet₂], p tau
  · rcases htarget with ⟨tau, htau, hp⟩
    have hcases := s.target_local_face_incidence_cases x y z hxyz htau
      ((Tet.containsTriple_eq_true tau x y z).2 hp)
    have closeInternal (u : Nat)
        (hi : SameTripleVertices x y z u s.d s.e)
        (hlocal :
          ([s.newTet₀, s.newTet₁, s.newTet₂].filter fun rho =>
            rho.ContainsTriple u s.d s.e).length = 2) :
        ((s.replace K).tets.filter p).length = 2 := by
      have hUzero : ((s.unchangedTets K).filter p).length = 0 := by
        have hempty : (s.unchangedTets K).filter p = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro rho hrho
          rcases List.mem_filter.mp hrho with ⟨hrho, hpRho⟩
          have hpRho : p rho := of_decide_eq_true hpRho
          have hrhoK := (hcore.move23Site_mem_unchangedTets s hlegal hrho).1
          apply hlegal.2.2 rho hrhoK
          have hdxyz := (hi s.d).2 (Or.inr (Or.inl rfl))
          have hexyz := (hi s.e).2 (Or.inr (Or.inr rfl))
          constructor
          · rcases hdxyz with rfl | rfl | rfl
            · exact hpRho.1
            · exact hpRho.2.1
            · exact hpRho.2.2
          · rcases hexyz with rfl | rfl | rfl
            · exact hpRho.1
            · exact hpRho.2.1
            · exact hpRho.2.2
        simp [hempty]
      have hxlocal := filter_containsTriple_length_eq_of_sameTripleVertices
        [s.newTet₀, s.newTet₁, s.newTet₂] hi
      rw [← hfilter] at hxlocal
      omega
    rcases hcases with hb | hb | hb | hb | hb | hb | hi | hi | hi
    · have hbal := s.boundaryFace_local_incidence_balance x y z (Or.inl hb)
      rw [← hfilter, ← hfilter] at hbal
      have hKcount := hKcount_of_source (by omega)
      omega
    · have hbal := s.boundaryFace_local_incidence_balance x y z (Or.inr (Or.inl hb))
      rw [← hfilter, ← hfilter] at hbal
      have hKcount := hKcount_of_source (by omega)
      omega
    · have hbal := s.boundaryFace_local_incidence_balance x y z (Or.inr (Or.inr (Or.inl hb)))
      rw [← hfilter, ← hfilter] at hbal
      have hKcount := hKcount_of_source (by omega)
      omega
    · have hbal := s.boundaryFace_local_incidence_balance x y z (Or.inr (Or.inr (Or.inr (Or.inl hb))))
      rw [← hfilter, ← hfilter] at hbal
      have hKcount := hKcount_of_source (by omega)
      omega
    · have hbal := s.boundaryFace_local_incidence_balance x y z (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb)))))
      rw [← hfilter, ← hfilter] at hbal
      have hKcount := hKcount_of_source (by omega)
      omega
    · have hbal := s.boundaryFace_local_incidence_balance x y z (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb)))))
      rw [← hfilter, ← hfilter] at hbal
      have hKcount := hKcount_of_source (by omega)
      omega
    · exact closeInternal s.a hi s.local_internal_ade.2
    · exact closeInternal s.b hi s.local_internal_bde.2
    · exact closeInternal s.c hi s.local_internal_cde.2
  · push Not at htarget
    have htargetZero :
        ([s.newTet₀, s.newTet₁, s.newTet₂].filter p).length = 0 := by
      have hempty : [s.newTet₀, s.newTet₁, s.newTet₂].filter p = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro rho hrho
        rcases List.mem_filter.mp hrho with ⟨hrho, hpRho⟩
        exact htarget rho hrho (of_decide_eq_true hpRho)
      simp [hempty]
    rcases hrepresented with ⟨tau, htau, hp⟩
    rw [s.replace_tets_eq] at htau
    simp only [List.mem_cons] at htau
    rcases htau with rfl | rfl | rfl | htau
    · exact (htarget s.newTet₀ (by simp) hp).elim
    · exact (htarget s.newTet₁ (by simp) hp).elim
    · exact (htarget s.newTet₂ (by simp) hp).elim
    · by_cases hsourceMem : ∃ rho ∈ [s.leftTet, s.rightTet], p rho
      · rcases hsourceMem with ⟨rho, hrho, hpRho⟩
        have hcases := s.source_local_face_incidence_cases x y z hxyz hrho
          ((Tet.containsTriple_eq_true rho x y z).2 hpRho)
        have closeBoundary
            (hb :
              SameTripleVertices x y z s.a s.b s.d ∨
              SameTripleVertices x y z s.a s.b s.e ∨
              SameTripleVertices x y z s.a s.c s.d ∨
              SameTripleVertices x y z s.a s.c s.e ∨
              SameTripleVertices x y z s.b s.c s.d ∨
              SameTripleVertices x y z s.b s.c s.e) :
            ((s.replace K).tets.filter p).length = 2 := by
          have hbal := s.boundaryFace_local_incidence_balance x y z hb
          rw [← hfilter, ← hfilter] at hbal
          have hKcount := hKcount_of_source (by omega)
          omega
        rcases hcases with hb | hb | hb | hb | hb | hb | hi
        · exact closeBoundary (Or.inl hb)
        · exact closeBoundary (Or.inr (Or.inl hb))
        · exact closeBoundary (Or.inr (Or.inr (Or.inl hb)))
        · exact closeBoundary (Or.inr (Or.inr (Or.inr (Or.inl hb))))
        · exact closeBoundary (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb)))))
        · exact closeBoundary (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb)))))
        have hlocal := s.local_internal_abc
        have hxlocal := filter_containsTriple_length_eq_of_sameTripleVertices
          [s.leftTet, s.rightTet] hi
        rw [← hfilter] at hxlocal
        have hKcount := hKcount_of_source (by omega)
        have htauFilter : tau ∈ (s.unchangedTets K).filter p := by
          exact List.mem_filter.mpr ⟨htau, by simpa [p] using hp⟩
        have hUpos : 0 < ((s.unchangedTets K).filter p).length :=
          List.length_pos_iff_exists_mem.mpr ⟨tau, htauFilter⟩
        omega
      · push Not at hsourceMem
        have hsourceZero :
            ([s.leftTet, s.rightTet].filter p).length = 0 := by
          have hempty : [s.leftTet, s.rightTet].filter p = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro rho hrho
            rcases List.mem_filter.mp hrho with ⟨hrho, hpRho⟩
            exact hsourceMem rho hrho (of_decide_eq_true hpRho)
          simp [hempty]
        have htauK := (hcore.move23Site_mem_unchangedTets s hlegal htau).1
        have hKcount := hcore.2.2 x y z hxyz ⟨tau, htauK, hp⟩
        change (K.tets.filter p).length = 2 at hKcount
        omega

end Poincare
