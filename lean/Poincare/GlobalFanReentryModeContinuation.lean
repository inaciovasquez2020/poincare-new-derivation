import Poincare.GlobalWitnessedReentryStateContinuation

namespace Poincare

/-- The two obstruction modes that remain after local no-degree-four source-face
classification: a high fan or a witnessed exact-three source-face reentry. -/
inductive FanReentryModeState (K : Triangulation) where
  | fan (state : HighFanState K)
  | reentry (state : WitnessedReentryState K)

/-- A high-fan or witnessed-reentry obstruction can always be continued
without assuming high edges are absent.  The only one-step exits are a legal
`2-3` move or strict topology-preserving `PhiSupport` descent; otherwise one
obtains another obstruction mode. -/
theorem ClosedTriangulationCore.exists_legal_move23_or_descent_or_next_fanReentryMode
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (q : FanReentryModeState K) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    Nonempty (FanReentryModeState K) := by
  cases q with
  | fan state =>
      rcases
          ClosedTriangulationCore.FanChordTransition.continue_reinjectHigh
            hcore hM hlinks hconn hNoFour state.transition with
        hmove23 | hdescent | hreentry | hfan

      · exact Or.inl hmove23
      · exact Or.inr (Or.inl hdescent)
      · obtain ⟨s, s', _hrealized, _hthree, hstep⟩ := hreentry
        exact
          Or.inr
            (Or.inr
              ⟨FanReentryModeState.reentry
                (witnessedReentryStateOfStep hstep)⟩)
      · obtain ⟨next⟩ := hfan
        exact
          Or.inr
            (Or.inr
              ⟨FanReentryModeState.fan next⟩)

  | reentry state =>
      rcases
          ClosedTriangulationCore.WitnessedReentryState.continue_reinjectHigh
            hcore hM hlinks hconn hNoFour state with
        hmove23 | hdescent | hreentry | hfan

      · exact Or.inl hmove23
      · exact Or.inr (Or.inl hdescent)
      · obtain ⟨next⟩ := hreentry
        exact
          Or.inr
            (Or.inr
              ⟨FanReentryModeState.reentry next⟩)
      · obtain ⟨next⟩ := hfan
        exact
          Or.inr
            (Or.inr
              ⟨FanReentryModeState.fan next⟩)

/-- In the incidence-four case, every realized exact-three candidate on the
old shared-face edge `(m.a,m.b)` after a legal `2-3` has absent source face.
Thus the candidate is a genuinely legal first `3-2` move. -/
theorem Move23Site.move32_candidate_sourceFaceAbsent_on_ab_after_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (s : Move32Site)
    (hsd : s.d = m.a)
    (hse : s.e = m.b)
    (hrealized : s.RealizedIn (m.replace K))
    (hthree : s.SharedEdgeExactlyThree (m.replace K)) :
    s.SourceFaceAbsent (m.replace K) := by
  have hends :=
    m.move32_candidate_sourceFace_contains_newEdgeEndpoints
      hcore hlegal s hsd hse hrealized hthree
  have hcNot :=
    m.move32_candidate_sourceFace_not_contains_oldThird
      hcore hlegal s hsd hse hrealized
  have hcore' : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hs := hcore'.move32Site_distinct s hrealized
  have hm := m.distinct
  simp [hsd, hse] at hs
  simp at hm
  simp only [List.mem_cons, List.mem_singleton] at hends hcNot
  intro tau htau hface
  rw [m.replace_tets_eq K] at htau
  simp only [List.mem_cons] at htau
  rcases htau with rfl | rfl | rfl | htau
  · simp [Move23Site.newTet₀, Tet.verts] at hface
    aesop
  · simp [Move23Site.newTet₁, Tet.verts] at hface
    aesop
  · simp [Move23Site.newTet₂, Tet.verts] at hface
    aesop
  · have hunchanged :=
      hcore.move23Site_mem_unchangedTets m hlegal htau
    have hsourceMem :
        ∀ z : Nat, z ∈ [s.a, s.b, s.c] → z ∈ tau.verts := by
      intro z hz
      simp only [List.mem_cons, List.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hface.1
      · exact hface.2.1
      · exact hface.2.2
    have hdTau : m.d ∈ tau.verts := hsourceMem m.d hends.1
    have heTau : m.e ∈ tau.verts := hsourceMem m.e hends.2
    exact hlegal.2.2 tau hunchanged.1 ⟨hdTau, heTau⟩

/-- A legal `2-3` move whose shared-face edge `(a,b)` has incidence four
therefore has a legal `3-2` continuation on that same edge. -/
theorem Move23Site.exists_legal_move32_on_ab_after_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4 :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 4) :
    ∃ s : Move32Site,
      s.d = m.a ∧
      s.e = m.b ∧
      s.LegalIn (m.replace K) := by
  obtain ⟨s, hsd, hse, hrealized, hthree⟩ :=
    m.exists_move32_candidate_on_ab_after_incidence_four
      hcore hlegal hinc4
  have habsent :=
    m.move32_candidate_sourceFaceAbsent_on_ab_after_incidence_four
      hcore hlegal s hsd hse hrealized hthree
  exact ⟨s, hsd, hse, hrealized, hthree, habsent⟩

end Poincare
