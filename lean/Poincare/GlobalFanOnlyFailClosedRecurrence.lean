import Poincare.GlobalFanReentryModeFiniteRecurrence
import Poincare.GlobalFanReentryModeLinkedSuccessor
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Poincare

/-- The fail-closed successor proof can be restricted to fan states. Unlike
an arbitrary mixed-mode step, the chosen successor is either an ordinary
chord successor or a source-face high-edge reinjection. -/
theorem ClosedTriangulationCore.exists_highFanStep_of_noMove23_noDescent
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
    (old : HighFanState K) :
    ∃ next : HighFanState K,
      FanReentryModeStep K (.fan old) (.fan next) := by
  have hconnected : ConnectedLinkClosedCore K :=
    connectedLinkClosedCore_of_topologicalThreeManifold K hcore hM
  have hlinks :
      ∀ v ∈ vertexSupport K, VertexLinkConnected K v :=
    hconnected.2
  have hconn : TetrahedronVertexOverlapConnected K :=
    hcore.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold hM
  have hNoFour :
      ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4 := by
    rcases
        hcore.exists_topology_preserving_PhiSupport_descent_or_no_degree_four
          hlinks hconn hphi with
      hdescent | hNoFour
    · exact (hNoDescent hdescent).elim
    · exact hNoFour
  rcases
      ClosedTriangulationCore.FanChordTransition.continue
        hcore hM hNoFour old.transition with
    hmove23 | hdescent | hobstruction | hnext
  · exact (hNoMove23 hmove23).elim
  · exact (hNoDescent hdescent).elim
  · obtain ⟨s, hsd, hse, hrealized, _hthree, hsource⟩ := hobstruction
    rcases
        hcore.exists_legal_move23_or_highFanState_away_from_edge_of_move32_sourceFace_obstruction_of_no_degree_four
          hM hlinks hNoFour s hrealized hsource old.v old.x old.endpoints_ne with
      hmove23 | hstate
    · exact (hNoMove23 hmove23).elim
    · obtain ⟨next, haway, hnonself⟩ := hstate
      exact ⟨next,
        FanReentryModeStep.fan_reinject
          old next s hsd hse hrealized hsource haway hnonself⟩
  · obtain ⟨T'⟩ := hnext
    let next : HighFanState K :=
      {
        v := old.transition.z0
        x := old.transition.z1
        v_supported := old.transition.z0_supported
        x_supported := old.transition.z1_supported
        endpoints_ne := old.transition.endpoints_ne
        transition := T'
      }
    exact ⟨next, FanReentryModeStep.fan_next old next rfl rfl⟩

/-- A pure high-fan trajectory exists without the global `hNoHigh`
assumption. Both chord continuation and source-face reinjection are allowed. -/
theorem ClosedTriangulationCore.exists_perpetual_highFanStep_of_noMove23_noDescent
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
    (start : HighFanState K) :
    ∃ states : Nat → HighFanState K,
      states 0 = start ∧
      (∀ n, FanReentryModeStep K (.fan (states n)) (.fan (states (n + 1)))) ∧
      ∀ n, (states (n + 1)).edgeState ≠ (states n).edgeState := by
  classical
  have hnext : ∀ q : HighFanState K,
      ∃ q' : HighFanState K,
        FanReentryModeStep K (.fan q) (.fan q') := by
    intro q
    exact hcore.exists_highFanStep_of_noMove23_noDescent
      hM hphi hNoMove23 hNoDescent q
  let step : HighFanState K → HighFanState K :=
    fun q => Classical.choose (hnext q)
  have hstep : ∀ q : HighFanState K,
      FanReentryModeStep K (.fan q) (.fan (step q)) := by
    intro q
    exact Classical.choose_spec (hnext q)
  let states : Nat → HighFanState K :=
    fun n => Nat.rec start (fun _ q => step q) n
  refine ⟨states, ?_, ?_, ?_⟩
  · simp [states]
  · intro n
    simpa [states] using hstep (states n)
  · intro n
    have hs : FanReentryModeStep K
        (.fan (states n)) (.fan (states (n + 1))) := by
      simpa [states] using hstep (states n)
    have hkey := hs.fan_to_fan_canonicalEdgeKey_ne
    intro hEq
    apply hkey
    have h := congrArg
      (fun e : SupportedEdgeState K => e.key) hEq
    simpa using h

/-- Recurrent high-fan edge state with the stronger reinjection-inclusive
lineage. This is a return of an edge key, NOT a complete geometric state,
and no prohibition of cycles is asserted. -/
theorem ClosedTriangulationCore.exists_recurrent_highFanStep_of_noMove23_noDescent
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
    (start : HighFanState K) :
    ∃ states : Nat → HighFanState K,
      ∃ i j : Nat,
        states 0 = start ∧
        i + 1 < j ∧
        j ≤ Fintype.card (SupportedEdgeState K) ∧
        (states i).edgeState = (states j).edgeState ∧
        (∀ n, i ≤ n → n < j →
          FanReentryModeStep K (.fan (states n)) (.fan (states (n + 1)))) ∧
        (∀ n, i ≤ n → n < j →
          (states (n + 1)).edgeState ≠ (states n).edgeState) := by
  classical
  obtain ⟨states, hzero, hstep, hprogress⟩ :=
    hcore.exists_perpetual_highFanStep_of_noMove23_noDescent
      hM hphi hNoMove23 hNoDescent start
  let N : Nat := Fintype.card (SupportedEdgeState K)
  let f : Nat → SupportedEdgeState K := fun n => (states n).edgeState
  let S : Finset Nat := Finset.range (N + 1)
  let T : Finset (SupportedEdgeState K) := Finset.univ
  have hcard : T.card < S.card := by
    simp [T, S, N]
  have hmaps : Set.MapsTo f
      (↑S : Set Nat) (↑T : Set (SupportedEdgeState K)) := by
    intro n hn
    simp [T]
  obtain ⟨i, hiS, j, hjS, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := S) (t := T) hcard hmaps
  have hiBound : i ≤ N := by
    have hiLt : i < N + 1 := by simpa [S] using hiS
    omega
  have hjBound : j ≤ N := by
    have hjLt : j < N + 1 := by simpa [S] using hjS
    omega
  have hconsecutive : ∀ n, f (n + 1) ≠ f n := by
    intro n
    simpa [f] using hprogress n
  rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt
  · have hgap : i + 1 < j := by
      by_contra hnot
      have hsucc : j = i + 1 := by omega
      subst j
      exact (hconsecutive i) hfij.symm
    refine ⟨states, i, j, hzero, hgap, ?_, ?_, ?_, ?_⟩
    · simpa [N] using hjBound
    · simpa [f] using hfij
    · intro n hin hnj
      exact hstep n
    · intro n hin hnj
      exact hprogress n
  · have hgap : j + 1 < i := by
      by_contra hnot
      have hsucc : i = j + 1 := by omega
      subst i
      exact (hconsecutive j) hfij
    refine ⟨states, j, i, hzero, hgap, ?_, ?_, ?_, ?_⟩
    · simpa [N] using hiBound
    · simpa [f] using hfij.symm
    · intro n hin hnj
      exact hstep n
    · intro n hin hnj
      exact hprogress n

end Poincare
