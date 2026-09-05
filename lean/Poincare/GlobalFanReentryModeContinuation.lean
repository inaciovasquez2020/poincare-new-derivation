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

end Poincare
