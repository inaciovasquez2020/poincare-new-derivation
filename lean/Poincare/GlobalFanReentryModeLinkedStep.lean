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

/-- The genuine next-chord output of the existing fan continuation
produces a linked fan-to-fan step, retaining both chord endpoints.
This handles only that output case; other continuation branches remain open. -/
theorem FanReentryModeStep.exists_fan_next_of_chord_successor
    {K : Triangulation}
    (old : HighFanState K)
    (hnext : Nonempty
      (FanChordTransition K old.transition.z0 old.transition.z1)) :
    ∃ next : HighFanState K,
      FanReentryModeStep K (.fan old) (.fan next) := by
  obtain ⟨T'⟩ := hnext
  let next : HighFanState K :=
    { v := old.transition.z0
      x := old.transition.z1
      v_supported := old.transition.z0_supported
      x_supported := old.transition.z1_supported
      endpoints_ne := old.transition.endpoints_ne
      transition := T' }
  exact ⟨next, FanReentryModeStep.fan_next old next rfl rfl⟩

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

/-- Each fully witnessed mixed fan/reentry transition changes its finite
mode-and-edge key. This is an adjacent-step geometric progress invariant,
not a global ranking function: longer recurrent cycles remain possible. -/
theorem FanReentryModeStep.finiteKey_ne
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {q r : FanReentryModeState K}
    (hstep : FanReentryModeStep K q r) :
    q.finiteKey hcore ≠ r.finiteKey hcore := by
  have hfan (old next : HighFanState K)
      (hne : canonicalEdgeKey next.v next.x ≠
        canonicalEdgeKey old.v old.x) :
      (FanReentryModeState.fan old).finiteKey hcore ≠
        (FanReentryModeState.fan next).finiteKey hcore := by
    intro hkey
    have hstates : old.edgeState = next.edgeState := by
      simpa [FanReentryModeState.finiteKey] using congrArg Prod.snd hkey
    have hkeys := congrArg (fun s : SupportedEdgeState K => s.key) hstates
    apply hne
    calc
      canonicalEdgeKey next.v next.x = next.edgeState.key :=
        next.edgeState_key.symm
      _ = old.edgeState.key := hkeys.symm
      _ = canonicalEdgeKey old.v old.x := old.edgeState_key
  cases hstep with
  | fan_next old next hv hx =>
      apply hfan
      rw [hv, hx]
      exact old.transition.canonicalEdgeKey_ne_old old.endpoints_ne
  | fan_reentry old s s' hsd hse hrealized hthree hstep =>
      intro hkey
      have htag : (false : Bool) = true := by
        simpa [FanReentryModeState.finiteKey] using congrArg Prod.fst hkey
      cases htag
  | fan_reinject old next s hsd hse hrealized hobstruction haway hnonself =>
      exact hfan old next haway
  | reentry_next old s' hstep =>
      intro hkey
      have hstep' := hstep.toSourceFaceReentry
      have hstates :
          sharedSupportedEdgeState hcore old.site old.realized =
            sharedSupportedEdgeState hcore s' hstep'.1 := by
        simpa [FanReentryModeState.finiteKey, witnessedReentryStateOfStep]
          using congrArg Prod.snd hkey
      have hne :=
        hcore.sharedSupportedEdgeState_ne_of_nonself
          old.site s' old.realized hstep'.1 hstep'.2.2.2
      exact hne hstates.symm
  | reentry_fan old next hnonself =>
      intro hkey
      have htag : (true : Bool) = false := by
        simpa [FanReentryModeState.finiteKey] using congrArg Prod.fst hkey
      cases htag

/-- A three-step fan-to-fan cycle makes a strict natural-valued ranking
on *all* linked mixed-mode transitions impossible. This theorem is conditional
on the three fully certified `HighFanState` transition witnesses; it does not
assert their existence for a particular fixed triangulation. -/
theorem FanReentryModeStep.no_nat_strict_ranking_of_three_fan_cycle
    {K : Triangulation} (a b c : HighFanState K)
    (hab : b.v = a.transition.z0 ∧ b.x = a.transition.z1)
    (hbc : c.v = b.transition.z0 ∧ c.x = b.transition.z1)
    (hca : a.v = c.transition.z0 ∧ a.x = c.transition.z1)
    (rank : FanReentryModeState K → Nat)
    (hstrict : ∀ {s t : FanReentryModeState K},
      FanReentryModeStep K s t → rank t < rank s) : False := by
  have h01 : rank (.fan b) < rank (.fan a) :=
    hstrict (FanReentryModeStep.fan_next a b hab.1 hab.2)
  have h12 : rank (.fan c) < rank (.fan b) :=
    hstrict (FanReentryModeStep.fan_next b c hbc.1 hbc.2)
  have h20 : rank (.fan a) < rank (.fan c) :=
    hstrict (FanReentryModeStep.fan_next c a hca.1 hca.2)
  omega

end Poincare
