import Poincare.GlobalFanReentryModeFiniteKey

namespace Poincare

/-- A lineage-preserving one-step relation for the mixed fan/reentry dynamics.

The existing coarse continuation theorem returns only `Nonempty
(FanReentryModeState K)`, which is enough for existence but forgets how the
new mode arose from the old one.  These constructors retain exactly the local
linkage needed by a later finite-state recurrence argument. -/
inductive FanReentryModeStep (K : Triangulation) :
    FanReentryModeState K → FanReentryModeState K → Prop where
  /-- Ordinary high-fan continuation follows the certified chord edge. -/
  | fan_next
      (old next : HighFanState K)
      (hv : next.v = old.transition.z0)
      (hx : next.x = old.transition.z1) :
      FanReentryModeStep K
        (.fan old) (.fan next)

  /-- An incidence-three fan chord enters witnessed source-face reentry. -/
  | fan_reentry
      (old : HighFanState K)
      (s s' : Move32Site)
      (hsd : s.d = old.transition.z0)
      (hse : s.e = old.transition.z1)
      (hrealized : s.RealizedIn K)
      (hthree : s.SharedEdgeExactlyThree K)
      (hstep : Move32SourceFaceWitnessedReentry K s s') :
      FanReentryModeStep K
        (.fan old)
        (.reentry (witnessedReentryStateOfStep hstep))

  /-- A source-face high edge found while continuing a fan is reinjected as a
  new high-fan state.  The edge is explicitly away from the old fan edge and
  nonself relative to the incidence-three chord site that exposed it. -/
  | fan_reinject
      (old next : HighFanState K)
      (s : Move32Site)
      (hsd : s.d = old.transition.z0)
      (hse : s.e = old.transition.z1)
      (hrealized : s.RealizedIn K)
      (hobstruction :
        ∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts)
      (haway :
        canonicalEdgeKey next.v next.x ≠
          canonicalEdgeKey old.v old.x)
      (hnonself :
        ¬ ((next.v = s.d ∧ next.x = s.e) ∨
           (next.v = s.e ∧ next.x = s.d))) :
      FanReentryModeStep K
        (.fan old) (.fan next)

  /-- A witnessed-reentry state advances by the certified witnessed reentry
  relation itself. -/
  | reentry_next
      (old : WitnessedReentryState K)
      (s' : Move32Site)
      (hstep : Move32SourceFaceWitnessedReentry K old.site s') :
      FanReentryModeStep K
        (.reentry old)
        (.reentry (witnessedReentryStateOfStep hstep))

  /-- A high edge exposed by a reentry state is reinjected as a high fan; its
  central edge is explicitly nonself relative to the old shared edge. -/
  | reentry_fan
      (old : WitnessedReentryState K)
      (next : HighFanState K)
      (hnonself :
        ¬ ((next.v = old.site.d ∧ next.x = old.site.e) ∨
           (next.v = old.site.e ∧ next.x = old.site.d))) :
      FanReentryModeStep K
        (.reentry old) (.fan next)

/-- Every linked fan-to-fan step changes the unordered central edge. -/
theorem FanReentryModeStep.fan_to_fan_canonicalEdgeKey_ne
    {K : Triangulation}
    {old next : HighFanState K}
    (hstep : FanReentryModeStep K (.fan old) (.fan next)) :
    canonicalEdgeKey next.v next.x ≠
      canonicalEdgeKey old.v old.x := by
  cases hstep with
  | fan_next old next hv hx =>
      rw [hv, hx]
      exact old.transition.canonicalEdgeKey_ne_old old.endpoints_ne
  | fan_reinject old next s hsd hse hrealized hobstruction haway hnonself =>
      exact haway

end Poincare
