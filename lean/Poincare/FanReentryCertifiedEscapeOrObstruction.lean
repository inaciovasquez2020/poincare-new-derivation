import Poincare.StabilizedFinitePathDescent
import Poincare.GlobalFanChordMove2332SecondStep

namespace Poincare

/-- Genuine three-move endpoint descent or a fully exposed second source-face
obstruction.  In the descent branch the three individual Pachner moves are
recorded as a certified finite path; existence is not inferred merely from a
homeomorphism.  No claim about universal high-fan/reentry termination is made. -/
theorem Move23Site.exists_certifiedPath_descent_or_second_sourceFace_obstruction
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4ab :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 4)
    (hinc4ac :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4) :
    (∃ L : Triangulation,
      ClosedTriangulationCore L ∧
      CertifiedPachnerPath K L ∧
      PhiSupport L < PhiSupport K) ∨
    ∃ s t : Move32Site,
      s.d = m.a ∧
      s.e = m.b ∧
      s.LegalIn (m.replace K) ∧
      t.d = m.a ∧
      t.e = m.c ∧
      t.RealizedIn (s.replace (m.replace K)) ∧
      t.SharedEdgeExactlyThree (s.replace (m.replace K)) ∧
      ∃ tau ∈ (s.replace (m.replace K)).tets,
        t.a ∈ tau.verts ∧
        t.b ∈ tau.verts ∧
        t.c ∈ tau.verts := by
  classical
  obtain ⟨s, hsd, hse, hslegal⟩ :=
    m.exists_legal_move32_on_ab_after_incidence_four
      hcore hlegal hinc4ab
  have hnotc : m.c ∉ [s.a, s.b, s.c] :=
    m.move32_candidate_sourceFace_not_contains_oldThird
      hcore hlegal s hsd hse hslegal.1
  obtain ⟨t, htd, hte, htrealized, htthree⟩ :=
    m.exists_second_move32_candidate_on_ac
      s hcore hlegal hinc4ac hsd hse hslegal hnotc
  by_cases habsent : t.SourceFaceAbsent (s.replace (m.replace K))
  · have hcore1 : ClosedTriangulationCore (m.replace K) :=
      hcore.move23Site_replace_closedCore m hlegal
    have hcore2 : ClosedTriangulationCore (s.replace (m.replace K)) :=
      hcore1.move32Site_replace_closedCore s hslegal
    have htlegal : t.LegalIn (s.replace (m.replace K)) :=
      ⟨htrealized, htthree, habsent⟩
    have hcore3 :
        ClosedTriangulationCore (t.replace (s.replace (m.replace K))) :=
      hcore2.move32Site_replace_closedCore t htlegal
    have hpath :
        CertifiedPachnerPath K
          (t.replace (s.replace (m.replace K))) :=
      CertifiedPachnerPath.snoc
        (CertifiedPachnerPath.snoc
          (CertifiedPachnerPath.snoc
            (CertifiedPachnerPath.refl K)
            (CertifiedPachnerStep.move23 hcore m hlegal))
          (CertifiedPachnerStep.move32 hcore1 s hslegal))
        (CertifiedPachnerStep.move32 hcore2 t htlegal)
    have hbalance :=
      move2332Block_PhiSupport_add_four_eq
        hcore m hlegal s hslegal hcore1 t htlegal hcore2 hcore3
    have hlt :
        PhiSupport (t.replace (s.replace (m.replace K))) <
          PhiSupport K := by
      omega
    exact Or.inl ⟨_, hcore3, hpath, hlt⟩
  · rw [Move32Site.SourceFaceAbsent] at habsent
    push_neg at habsent
    exact Or.inr
      ⟨s, t, hsd, hse, hslegal, htd, hte,
        htrealized, htthree, habsent⟩

end Poincare
