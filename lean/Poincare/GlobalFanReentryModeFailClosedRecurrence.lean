import Poincare.GlobalFanReentryModeFiniteRecurrence

namespace Poincare

/-- Under the fail-closed no-move/no-descent hypotheses, every initial mixed
fan/reentry mode lies on an infinite lineage-preserving trajectory with a
finite recurrent mode key.  The recurrent interval retains every certified
`FanReentryModeStep`.

This is still only a recurrence reduction: no impossibility of the recurrent
mixed-mode segment is claimed here. -/
theorem ClosedTriangulationCore.exists_recurrent_fanReentryModeKey_of_noMove23_noDescent
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (start : FanReentryModeState K) :
    ∃ states : Nat → FanReentryModeState K,
      ∃ i j,
        states 0 = start ∧
        i < j ∧
        j ≤ Fintype.card (FanReentryModeKey K) ∧
        (states i).finiteKey hcore = (states j).finiteKey hcore ∧
        ∀ n,
          i ≤ n →
          n < j →
          FanReentryModeStep K (states n) (states (n + 1)) := by
  obtain ⟨states, hzero, hstep⟩ :=
    hcore.exists_perpetual_fanReentryMode_trajectory_of_noMove23_noDescent
      hM hphi hNoMove23 hNoDescent start

  obtain ⟨i, j, hij, hbound, hkey, hsegment⟩ :=
    exists_recurrent_fanReentryModeKey hcore states hstep

  exact
    ⟨states, i, j, hzero, hij, hbound, hkey, hsegment⟩

end Poincare
