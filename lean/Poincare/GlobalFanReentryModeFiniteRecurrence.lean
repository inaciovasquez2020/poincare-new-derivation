import Poincare.GlobalFanReentryModePerpetualTrajectory
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Poincare

/-- Every infinite linked mixed fan/reentry trajectory has a recurrent finite
mode key among the first `card + 1` states.  The whole recurrent interval
retains the certified `FanReentryModeStep` lineage.

This is a finite recurrence reduction only; it does not assert that the
resulting mixed-mode cycle is impossible. -/
theorem exists_recurrent_fanReentryModeKey
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (states : Nat → FanReentryModeState K)
    (hstep :
      ∀ n,
        FanReentryModeStep K (states n) (states (n + 1))) :
    ∃ i j,
      i < j ∧
      j ≤ Fintype.card (FanReentryModeKey K) ∧
      (states i).finiteKey hcore = (states j).finiteKey hcore ∧
      ∀ n,
        i ≤ n →
        n < j →
        FanReentryModeStep K (states n) (states (n + 1)) := by
  classical

  let N : Nat :=
    Fintype.card (FanReentryModeKey K)

  let f : Nat → FanReentryModeKey K :=
    fun n => (states n).finiteKey hcore

  let S : Finset Nat :=
    Finset.range (N + 1)

  let T : Finset (FanReentryModeKey K) :=
    Finset.univ

  have hcard : T.card < S.card := by
    simpa [T, S, N]

  have hmaps :
      Set.MapsTo
        f
        (↑S : Set Nat)
        (↑T : Set (FanReentryModeKey K)) := by
    intro n hn
    simp [T]

  obtain
      ⟨i, hiS,
        j, hjS,
        hij,
        hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := S)
      (t := T)
      hcard
      hmaps

  have hiBound : i ≤ N := by
    have hiLt : i < N + 1 := by
      simpa [S] using hiS
    omega

  have hjBound : j ≤ N := by
    have hjLt : j < N + 1 := by
      simpa [S] using hjS
    omega

  rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt

  · refine ⟨i, j, hijlt, ?_, ?_, ?_⟩
    · simpa [N] using hjBound
    · simpa [f] using hfij
    · intro n hin hnj
      exact hstep n

  · refine ⟨j, i, hjilt, ?_, ?_, ?_⟩
    · simpa [N] using hiBound
    · simpa [f] using hfij.symm
    · intro n hjn hni
      exact hstep n

/-- The recurrent mixed-mode interval also retains genuine edge progress on
every fan-to-fan step.  In particular, whether the fan successor is the
ordinary chord continuation or a reinjected high source edge, its unordered
central edge differs from the old fan edge. -/
theorem exists_recurrent_fanReentryModeKey_with_fanProgress
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (states : Nat → FanReentryModeState K)
    (hstep :
      ∀ n,
        FanReentryModeStep K (states n) (states (n + 1))) :
    ∃ i j,
      i < j ∧
      j ≤ Fintype.card (FanReentryModeKey K) ∧
      (states i).finiteKey hcore = (states j).finiteKey hcore ∧
      (∀ n,
        i ≤ n →
        n < j →
        FanReentryModeStep K (states n) (states (n + 1))) ∧
      ∀ n old next,
        i ≤ n →
        n < j →
        states n = .fan old →
        states (n + 1) = .fan next →
        canonicalEdgeKey next.v next.x ≠
          canonicalEdgeKey old.v old.x := by
  obtain ⟨i, j, hij, hbound, hkey, hsegment⟩ :=
    exists_recurrent_fanReentryModeKey hcore states hstep

  refine ⟨i, j, hij, hbound, hkey, hsegment, ?_⟩
  intro n old next hin hnj hold hnext
  have hlink := hsegment n hin hnj
  rw [hold, hnext] at hlink
  exact hlink.fan_to_fan_canonicalEdgeKey_ne

end Poincare
