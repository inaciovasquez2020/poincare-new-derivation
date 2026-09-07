import Poincare.GlobalFanChordMove2332AutomaticSourceFaceClassification
import Poincare.GlobalFanReentryModeContinuation
import Poincare.GlobalHighEdgeToFanState

namespace Poincare

/-- The automatic incidence-four Move2332 branch can be reinjected into the
existing obstruction dynamics.  After the original strict-descent exit, the
post-prefix nonself-high alternative either exposes a legal `2-3` move or
becomes a high-fan state, while witnessed source-face reentry becomes the
reentry mode directly.  The constructed first/second Move32 data are retained
explicitly. -/
theorem Move23Site.exists_original_descent_or_prefix_legal_move23_or_fanReentryMode_of_ab_ac_incidence_four
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
      ((∃ m' : Move23Site,
        m'.LegalIn (s.replace (m.replace K))) ∨
      Nonempty (FanReentryModeState (s.replace (m.replace K)))) := by
  rcases
      m.exists_original_descent_or_prefix_nonself_high_or_witnessedReentry_of_ab_ac_incidence_four
        hcore hM hlegal hphi hinc4ab hinc4ac with
    hdescent | hprefix
  · exact Or.inl hdescent
  · obtain ⟨s, t, hsd, hse, hslegal, htd, hte, htrealized, htthree,
        hmode⟩ := hprefix
    have hcore1 : ClosedTriangulationCore (m.replace K) :=
      hcore.move23Site_replace_closedCore m hlegal
    have hcore2 : ClosedTriangulationCore (s.replace (m.replace K)) :=
      hcore1.move32Site_replace_closedCore s hslegal
    have hM2 :
        TriangulationRealizationIsClosedConnectedTopologicalThreeManifold
          (s.replace (m.replace K)) :=
      (m.first_move32_prefix_topological_package
        s hcore hM hlegal hslegal).1
    rcases hmode with hhigh | hreentry
    · obtain ⟨x, y, sigma, hxy, hsigma, hx, hy, _hnonself, hinc⟩ := hhigh
      have hinc' :
          4 ≤ ((s.replace (m.replace K)).tets.filter
            (fun gamma => x ∈ gamma.verts ∧ y ∈ gamma.verts)).length := by
        simpa using hinc
      rcases
          hcore2.exists_legal_move23_or_highFanState_of_edgeIncidence_four_le
            hM2 hxy hsigma hx hy hinc' with
        hmove23 | hfan
      · exact
          Or.inr
            ⟨s, t, hsd, hse, hslegal, htd, hte, htrealized, htthree,
              Or.inl hmove23⟩
      · obtain ⟨state⟩ := hfan
        exact
          Or.inr
            ⟨s, t, hsd, hse, hslegal, htd, hte, htrealized, htthree,
              Or.inr ⟨FanReentryModeState.fan state⟩⟩
    · exact
        Or.inr
          ⟨s, t, hsd, hse, hslegal, htd, hte, htrealized, htthree,
            Or.inr
              ⟨FanReentryModeState.reentry
                (witnessedReentryStateOfStep hreentry)⟩⟩

end Poincare
