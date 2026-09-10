import Poincare.GlobalFanChordMove2332SecondStep
import Poincare.GlobalFanChordMove2332PrefixSourceFaceOriginalDescent

namespace Poincare

/-- Incidence four on both old shared-face edges now closes the automatic
second-step fork through the source-face classifier.  Under honest manifoldness
and positive original support defect, the branch yields either a strict
homeomorphism-preserving descent from the original triangulation, or explicit
first/second Move32 data whose prefix state carries a nonself high edge or a
witnessed source-face reentry. -/
theorem Move23Site.exists_original_descent_or_prefix_nonself_high_or_witnessedReentry_of_ab_ac_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlegal : m.LegalIn K)
    (hphi : 0 < PhiSupport K)
    (hinc4ab :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 4)
    (hinc4ac :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    ∃ s t : Move32Site,
      s.d = m.a ∧
      s.e = m.b ∧
      s.LegalIn (m.replace K) ∧
      t.d = m.a ∧
      t.e = m.c ∧
      t.RealizedIn (s.replace (m.replace K)) ∧
      t.SharedEdgeExactlyThree (s.replace (m.replace K)) ∧
      ((∃ x y sigma,
        x ≠ y ∧
        sigma ∈ (s.replace (m.replace K)).tets ∧
        x ∈ sigma.verts ∧
        y ∈ sigma.verts ∧
        ¬ ((x = t.d ∧ y = t.e) ∨
           (x = t.e ∧ y = t.d)) ∧
        4 ≤
          ((s.replace (m.replace K)).tets.filter
            (fun gamma =>
              decide
                (x ∈ gamma.verts ∧
                 y ∈ gamma.verts))).length) ∨
      ∃ t' : Move32Site,
        Move32SourceFaceWitnessedReentry (s.replace (m.replace K)) t t') := by
  rcases
      m.exists_move2332_descent_or_second_sourceFace_obstruction_of_ab_ac_incidence_four
        hcore hlegal hinc4ab hinc4ac with
    hdescent | hobstruction
  · exact Or.inl hdescent
  · obtain ⟨s, t, hsd, hse, hslegal, htd, hte, htrealized, htthree,
        hobstruction⟩ := hobstruction
    rcases
        m.first_move32_prefix_exists_original_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction_of_original_PhiSupport_pos
          s t hcore hM hlegal hslegal hphi htrealized hobstruction with
      hdescent | hhigh | hreentry
    · exact Or.inl hdescent
    · exact
        Or.inr
          ⟨s, t, hsd, hse, hslegal, htd, hte, htrealized, htthree,
            Or.inl hhigh⟩
    · exact
        Or.inr
          ⟨s, t, hsd, hse, hslegal, htd, hte, htrealized, htthree,
            Or.inr hreentry⟩

end Poincare
