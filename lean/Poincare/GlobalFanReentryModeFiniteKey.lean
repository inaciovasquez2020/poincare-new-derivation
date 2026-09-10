import Poincare.GlobalFanReentryModeManifoldPositiveSupportContinuation
import Poincare.GlobalMove32SupportedEdgeState

namespace Poincare

/-- A finite key for the mixed obstruction dynamics.  The Boolean records the
mode kind (`false` = high fan, `true` = witnessed reentry), while the second
component is the canonical supported edge carried by that mode. -/
def FanReentryModeKey (K : Triangulation) :=
  Bool × SupportedEdgeState K

noncomputable instance fanReentryModeKeyFintype
    (K : Triangulation) :
    Fintype (FanReentryModeKey K) := by
  unfold FanReentryModeKey
  infer_instance

/-- Forget a mixed fan/reentry mode to its finite mode-kind plus supported-edge
key.  This is the finite state space used by the later recurrence reduction. -/
def FanReentryModeState.finiteKey
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (q : FanReentryModeState K) :
    FanReentryModeKey K :=
  match q with
  | .fan state =>
      (false, state.edgeState)
  | .reentry state =>
      (true,
        sharedSupportedEdgeState
          hcore state.site state.realized)

@[simp]
theorem FanReentryModeState.finiteKey_fan
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (state : HighFanState K) :
    (FanReentryModeState.fan state).finiteKey hcore =
      (false, state.edgeState) := by
  rfl

@[simp]
theorem FanReentryModeState.finiteKey_reentry
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (state : WitnessedReentryState K) :
    (FanReentryModeState.reentry state).finiteKey hcore =
      (true,
        sharedSupportedEdgeState
          hcore state.site state.realized) := by
  rfl

end Poincare
