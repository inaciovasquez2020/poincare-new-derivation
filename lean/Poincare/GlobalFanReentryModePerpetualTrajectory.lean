import Poincare.GlobalFanReentryModeLinkedSuccessor

namespace Poincare

/-- Under the fail-closed no-move/no-descent hypotheses, every initial mixed
fan/reentry mode extends to an infinite lineage-preserving trajectory. -/
theorem ClosedTriangulationCore.exists_perpetual_fanReentryMode_trajectory_of_noMove23_noDescent
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
      states 0 = start ∧
      ∀ n,
        FanReentryModeStep K (states n) (states (n + 1)) := by
  classical

  have hnext :
      ∀ q : FanReentryModeState K,
        ∃ q' : FanReentryModeState K,
          FanReentryModeStep K q q' := by
    intro q
    exact
      hcore.exists_fanReentryModeStep_of_noMove23_noDescent
        hM hphi hNoMove23 hNoDescent q

  let step : FanReentryModeState K → FanReentryModeState K :=
    fun q => Classical.choose (hnext q)

  have hstep :
      ∀ q : FanReentryModeState K,
        FanReentryModeStep K q (step q) := by
    intro q
    exact Classical.choose_spec (hnext q)

  let states : Nat → FanReentryModeState K :=
    fun n => Nat.rec start (fun _ q => step q) n

  refine ⟨states, ?_, ?_⟩
  · simp [states]
  · intro n
    simpa [states] using hstep (states n)

end Poincare
