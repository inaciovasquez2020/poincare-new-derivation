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

/-- OPEN OBLIGATION, NOT A PROVED THEOREM.

Under the simply-connected no-Move23/no-topology-preserving-descent branch,
exclude an actual finite recurrent interval of linked mixed fan/reentry
states. The complete `FanReentryModeState` values (fan transitions or
witnessed Move32 reentry sites) and every `FanReentryModeStep` proof are
retained; equality of `finiteKey` is only the finite recurrence trigger.

No PL-sphere recognition or Poincare theorem is assumed. This condition
has not been established from the geometric hypotheses. -/
def SimplyConnectedFullWitnessRecurrentCycleEscape : Prop :=
  ∀ (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (_hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (_hSC : TriangulationRealizationSimplyConnected K)
    (_hPhi : 0 < PhiSupport K)
    (_hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (_hNoDescent :
      ¬ ∃ L : Triangulation,
        ClosedTriangulationCore L ∧
        PhiSupport L < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier L)),
    ∀ (states : Nat → FanReentryModeState K) (i j : Nat),
      i < j →
      j ≤ Fintype.card (FanReentryModeKey K) →
      (states i).finiteKey hcore = (states j).finiteKey hcore →
      (∀ n, i ≤ n → n < j →
        FanReentryModeStep K (states n) (states (n + 1))) →
      False

end Poincare
