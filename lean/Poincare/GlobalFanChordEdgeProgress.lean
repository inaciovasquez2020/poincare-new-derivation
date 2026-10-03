import Poincare.GlobalFanChordTransition
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Poincare

/-- A high fan-chord step cannot keep the same unordered central edge.
The transition witness contains both chord endpoints, while by construction it
misses at least one endpoint of the old central edge. -/
theorem FanChordTransition.canonicalEdgeKey_ne_old
    {K : Triangulation} {v x : Nat}
    (T : FanChordTransition K v x)
    (hvx : v ≠ x) :
    canonicalEdgeKey T.z0 T.z1 ≠ canonicalEdgeKey v x := by
  intro hkey
  rcases
      (canonicalEdgeKey_eq_iff
        T.z0 T.z1 v x T.endpoints_ne hvx).1 hkey with
    hdirect | hreverse
  · rcases hdirect with ⟨hz0, hz1⟩
    rcases T.escapes_old_edge with hv | hx
    · apply hv
      simpa [hz0] using T.z0_mem
    · apply hx
      simpa [hz1] using T.z1_mem
  · rcases hreverse with ⟨hz0, hz1⟩
    rcases T.escapes_old_edge with hv | hx
    · apply hv
      simpa [hz1] using T.z1_mem
    · apply hx
      simpa [hz0] using T.z0_mem

/-- A finite-state package for one central edge carrying a fan-chord
transition.  The transition itself certifies the chord that becomes the next
central edge in the perpetual high-incidence branch. -/
structure HighFanState (K : Triangulation) where
  v : Nat
  x : Nat
  v_supported : v ∈ vertexSupport K
  x_supported : x ∈ vertexSupport K
  endpoints_ne : v ≠ x
  transition : FanChordTransition K v x

/-- Canonical finite supported-edge state of the current high fan. -/
def HighFanState.edgeState
    {K : Triangulation} (q : HighFanState K) :
    SupportedEdgeState K :=
  supportedEdgeStateOfDistinct
    K q.v q.x q.v_supported q.x_supported q.endpoints_ne

@[simp]
theorem HighFanState.edgeState_key
    {K : Triangulation} (q : HighFanState K) :
    q.edgeState.key = canonicalEdgeKey q.v q.x := by
  exact
    supportedEdgeStateOfDistinct_key
      K q.v q.x q.v_supported q.x_supported q.endpoints_ne

/-- If legal `2-3` moves and strict `PhiSupport` descent are globally excluded,
and the source-obstruction high-edge alternative is excluded in the exact
form consumed by `FanChordTransition.continue_noHigh`, then every high fan
state has another high fan state.  The resulting infinite sequence changes
its finite supported-edge state at every step.

This theorem does not yet exclude a nonconsecutive return to an earlier edge
state. -/
theorem
    ClosedTriangulationCore.exists_perpetual_highFanState_of_noMove23_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (hNoMove23 :
      ¬ ∃ m : Move23Site,
        m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ p q sigma,
          p ≠ q ∧
          sigma ∈ K.tets ∧
          p ∈ sigma.verts ∧
          q ∈ sigma.verts ∧
          ¬ ((p = s.d ∧ q = s.e) ∨
             (p = s.e ∧ q = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (p ∈ gamma.verts ∧
                   q ∈ gamma.verts))).length)
    (start : HighFanState K) :
    ∃ states : Nat → HighFanState K,
      states 0 = start ∧
      (∀ n,
        (states (n + 1)).v = (states n).transition.z0 ∧
        (states (n + 1)).x = (states n).transition.z1) ∧
      ∀ n,
        (states (n + 1)).edgeState ≠
          (states n).edgeState := by
  classical

  have hnext :
      ∀ q : HighFanState K,
        ∃ q' : HighFanState K,
          q'.v = q.transition.z0 ∧
          q'.x = q.transition.z1 ∧
          q'.edgeState ≠ q.edgeState := by
    intro q
    rcases
        ClosedTriangulationCore.FanChordTransition.continue_noHigh
          hcore hM hlinks hNoFour hNoHigh q.transition with
      hmove23 | hdescent | hnextTransition

    · exact (hNoMove23 hmove23).elim

    · exact (hNoDescent hdescent).elim

    · obtain ⟨T'⟩ := hnextTransition

      let q' : HighFanState K :=
        {
          v := q.transition.z0
          x := q.transition.z1
          v_supported := q.transition.z0_supported
          x_supported := q.transition.z1_supported
          endpoints_ne := q.transition.endpoints_ne
          transition := T'
        }

      refine ⟨q', rfl, rfl, ?_⟩
      intro hstate

      have hkey :=
        congrArg
          (fun r : SupportedEdgeState K => r.key)
          hstate

      exact
        q.transition.canonicalEdgeKey_ne_old q.endpoints_ne
          (by
            simpa [q', HighFanState.edgeState] using hkey)

  let step : HighFanState K → HighFanState K :=
    fun q => Classical.choose (hnext q)

  have hstep :
      ∀ q : HighFanState K,
        (step q).v = q.transition.z0 ∧
        (step q).x = q.transition.z1 ∧
        (step q).edgeState ≠ q.edgeState := by
    intro q
    exact Classical.choose_spec (hnext q)

  let seq : Nat → HighFanState K :=
    fun n => Nat.rec start (fun _ q => step q) n

  refine ⟨seq, ?_, ?_, ?_⟩

  · simp [seq]

  · intro n
    constructor
    · simpa [seq] using (hstep (seq n)).1
    · simpa [seq] using (hstep (seq n)).2.1

  · intro n
    simpa [seq] using (hstep (seq n)).2.2

/-- Every perpetual high-fan state sequence with genuine edge progress has a
nonconsecutive recurrent canonical supported-edge state among the first
`card + 1` states.  The whole recurrent segment retains the certified
fan-chord endpoint transition and consecutive edge-state inequality.

This is only a finite recurrence theorem; it does not assert that the return
cycle is impossible. -/
theorem exists_recurrent_highFanEdgeState
    {K : Triangulation}
    (states : Nat → HighFanState K)
    (hstep :
      ∀ n,
        (states (n + 1)).v = (states n).transition.z0 ∧
        (states (n + 1)).x = (states n).transition.z1)
    (hconsecutive :
      ∀ n,
        (states (n + 1)).edgeState ≠
          (states n).edgeState) :
    ∃ i j,
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      (states i).edgeState = (states j).edgeState ∧
      (∀ n,
        i ≤ n →
        n < j →
        (states (n + 1)).v = (states n).transition.z0 ∧
        (states (n + 1)).x = (states n).transition.z1) ∧
      ∀ n,
        i ≤ n →
        n < j →
        (states (n + 1)).edgeState ≠
          (states n).edgeState := by
  classical

  let N : Nat :=
    Fintype.card (SupportedEdgeState K)

  let f : Nat → SupportedEdgeState K :=
    fun n => (states n).edgeState

  let S : Finset Nat :=
    Finset.range (N + 1)

  let T : Finset (SupportedEdgeState K) :=
    Finset.univ

  have hcard : T.card < S.card := by
    simpa [T, S, N]

  have hmaps :
      Set.MapsTo
        f
        (↑S : Set Nat)
        (↑T : Set (SupportedEdgeState K)) := by
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

  have hconsecutive' :
      ∀ n,
        f (n + 1) ≠ f n := by
    intro n
    simpa [f] using hconsecutive n

  rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt

  · have hgap : i + 1 < j := by
      by_contra hnot
      have hsucc : j = i + 1 := by
        omega
      subst j
      exact (hconsecutive' i) hfij.symm

    refine ⟨i, j, hgap, ?_, ?_, ?_, ?_⟩
    · simpa [N] using hjBound
    · simpa [f] using hfij
    · intro n hin hnj
      exact hstep n
    · intro n hin hnj
      exact hconsecutive n

  · have hgap : j + 1 < i := by
      by_contra hnot
      have hsucc : i = j + 1 := by
        omega
      subst i
      exact (hconsecutive' j) hfij

    refine ⟨j, i, hgap, ?_, ?_, ?_, ?_⟩
    · simpa [N] using hiBound
    · simpa [f] using hfij.symm
    · intro n hjn hni
      exact hstep n
    · intro n hjn hni
      exact hconsecutive n

/-- A local high-fan transition location, retaining the oriented central edge
and the actual adjacent link-star pair that realizes the transition. -/
structure HighFanLocation (K : Triangulation) where
  v : SupportedVertexState K
  x : SupportedVertexState K
  endpoints_ne : (v : Nat) ≠ (x : Nat)
  sigma :
    {t : LinkTriangle //
      t ∈ vertexLinkStarTriangles K v x}
  rho :
    {t : LinkTriangle //
      t ∈ vertexLinkStarTriangles K v x}
  adjacent :
    (vertexLinkStarGraph K v x).Adj sigma rho

/-- The local location type is finite because both represented endpoints and
each represented vertex-link star carrier are finite. -/
noncomputable instance highFanLocationFintype
    (K : Triangulation) :
    Fintype (HighFanLocation K) := by
  classical
  letI : Finite (HighFanLocation K) := by
    apply Finite.of_injective
      (f := fun q =>
        (⟨q.v, ⟨q.x, (q.sigma, q.rho)⟩⟩ :
          Σ v : SupportedVertexState K,
          Σ x : SupportedVertexState K,
            ({t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x} ×
              {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x})))
    intro a b h
    cases a with
    | mk av ax ane as ar aadj =>
      cases b with
      | mk bv bx bne bs br badj =>
        rcases h with ⟨rfl, rfl⟩
        rfl
  exact Fintype.ofFinite (HighFanLocation K)

/-- Every high-fan state determines a unique retained local transition
location. -/
def HighFanState.location
    {K : Triangulation}
    (q : HighFanState K) :
    HighFanLocation K :=
  {
    v :=
      ⟨q.v, List.mem_toFinset.mpr q.v_supported⟩
    x :=
      ⟨q.x, List.mem_toFinset.mpr q.x_supported⟩
    endpoints_ne := q.endpoints_ne
    sigma := q.transition.sigma
    rho := q.transition.rho
    adjacent := q.transition.adjacent
  }

/-- Equality of retained local locations identifies the oriented central edge
and the actual adjacent transition pair. -/
theorem HighFanState.location_eq_iff
    {K : Triangulation}
    (q r : HighFanState K) :
    q.location = r.location ↔
      q.v = r.v ∧
      q.x = r.x ∧
      q.transition.sigma.1 = r.transition.sigma.1 ∧
      q.transition.rho.1 = r.transition.rho.1 := by
  constructor
  · intro h
    have hv := congrArg (fun s : HighFanLocation K => (s.v : Nat)) h
    have hx := congrArg (fun s : HighFanLocation K => (s.x : Nat)) h
    have hs := congrArg (fun s : HighFanLocation K => s.sigma.1) h
    have hr := congrArg (fun s : HighFanLocation K => s.rho.1) h
    exact ⟨hv, hx, hs, hr⟩
  · rintro ⟨hv, hx, hs, hr⟩
    have location_ext :
        ∀ (a b : HighFanLocation K),
          (a.v : Nat) = (b.v : Nat) →
          (a.x : Nat) = (b.x : Nat) →
          a.sigma.1 = b.sigma.1 →
          a.rho.1 = b.rho.1 →
          a = b := by
      intro a b hav hab has har
      cases a with
      | mk av ax ane as ar aadj =>
        cases b with
        | mk bv bx bne bs br badj =>
          have hv' : av = bv := Subtype.ext hav
          have hx' : ax = bx := Subtype.ext hab
          cases hv'
          cases hx'
          have hσ : as = bs := Subtype.ext has
          have hρ : ar = br := Subtype.ext har
          cases hσ
          cases hρ
          rfl
    exact location_ext q.location r.location hv hx hs hr

/-- A perpetual high-fan state sequence with genuine edge progress has a
nonconsecutive recurrent retained local transition location.  The recurrence
is finite-state only; it does not assert that the resulting return cycle is
impossible. -/
theorem EXISTS_RECURRENT_LOCAL_FAN_CONFIGURATION
    {K : Triangulation}
    (states : Nat → HighFanState K)
    (hstep :
      ∀ n,
        (states (n + 1)).v = (states n).transition.z0 ∧
        (states (n + 1)).x = (states n).transition.z1)
    (hconsecutive :
      ∀ n,
        (states (n + 1)).edgeState ≠
          (states n).edgeState) :
    ∃ i j,
      i + 1 < j ∧
      j ≤ Fintype.card (HighFanLocation K) ∧
      (states i).location = (states j).location ∧
      (∀ n,
        i ≤ n →
        n < j →
        (states (n + 1)).v = (states n).transition.z0 ∧
        (states (n + 1)).x = (states n).transition.z1) ∧
      ∀ n,
        i ≤ n →
        n < j →
        (states (n + 1)).edgeState ≠
          (states n).edgeState := by
  classical

  have hlocation_consecutive :
      ∀ n,
        (states (n + 1)).location ≠
          (states n).location := by
    intro n hloc
    have hvx :=
      (HighFanState.location_eq_iff
        (states (n + 1))
        (states n)).1 hloc

    have hkey :
        (states (n + 1)).edgeState.key =
          (states n).edgeState.key := by
      calc
        (states (n + 1)).edgeState.key =
            canonicalEdgeKey
              (states (n + 1)).v
              (states (n + 1)).x :=
          HighFanState.edgeState_key (states (n + 1))

        _ =
            canonicalEdgeKey
              (states n).v
              (states n).x := by
          rw [hvx.1, hvx.2.1]

        _ =
            (states n).edgeState.key :=
          (HighFanState.edgeState_key (states n)).symm

    have hedge_ext :
        ∀ a b : SupportedEdgeState K,
          a.key = b.key →
          a = b := by
      intro a b hab
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hab
      · apply Subtype.ext
        exact congrArg Prod.snd hab

    exact
      (hconsecutive n)
        (hedge_ext _ _ hkey)

  let N : Nat :=
    Fintype.card (HighFanLocation K)

  let f : Nat → HighFanLocation K :=
    fun n => (states n).location

  let S : Finset Nat :=
    Finset.range (N + 1)

  let T : Finset (HighFanLocation K) :=
    Finset.univ

  have hcard : T.card < S.card := by
    simpa [T, S, N]

  have hmaps :
      Set.MapsTo
        f
        (↑S : Set Nat)
        (↑T : Set (HighFanLocation K)) := by
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

  have hconsecutive' :
      ∀ n,
        f (n + 1) ≠ f n := by
    intro n
    simpa [f] using hlocation_consecutive n

  rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt

  · have hgap : i + 1 < j := by
      by_contra hnot
      have hsucc : j = i + 1 := by
        omega
      subst j
      exact (hconsecutive' i) hfij.symm

    refine ⟨i, j, hgap, ?_, ?_, ?_, ?_⟩
    · simpa [N] using hjBound
    · simpa [f] using hfij
    · intro n hin hnj
      exact hstep n
    · intro n hin hnj
      exact hconsecutive n

  · have hgap : j + 1 < i := by
      by_contra hnot
      have hsucc : i = j + 1 := by
        omega
      subst i
      exact (hconsecutive' j) hfij

    refine ⟨j, i, hgap, ?_, ?_, ?_, ?_⟩
    · simpa [N] using hiBound
    · simpa [f] using hfij.symm
    · intro n hjn hni
      exact hstep n
    · intro n hjn hni
      exact hconsecutive n

/-- A repeated retained local fan location has a unique transverse
carrier. -/
theorem FanChordTransition.same_location_transverse_eq
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (T0 T1 : FanChordTransition K v x)
    (hσ : T0.sigma.1 = T1.sigma.1)
    (hρ : T0.rho.1 = T1.rho.1) :
    T0.transverse = T1.transverse := by
  by_contra hy
  exact
    T0.same_location_different_transverse_impossible
      hcore T1 hσ hρ hy

/-- On the no-high branch, ruling out exactly the finite recurrent high-fan
segment certified above forces genuine global progress: either a legal `2-3`
move or strict `PhiSupport` descent.  This isolates the remaining high-fan
cycle obstruction without asserting that such cycles are impossible. -/
theorem
    ClosedTriangulationCore.exists_move23_or_descent_of_noHigh_no_recurrent_highFan_cycle
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ p q sigma,
          p ≠ q ∧
          sigma ∈ K.tets ∧
          p ∈ sigma.verts ∧
          q ∈ sigma.verts ∧
          ¬ ((p = s.d ∧ q = s.e) ∨
             (p = s.e ∧ q = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (p ∈ gamma.verts ∧
                   q ∈ gamma.verts))).length)
    (start : HighFanState K)
    (hNoCycle :
      ¬ ∃ (states : Nat → HighFanState K) (i j : Nat),
        i + 1 < j ∧
        j ≤ Fintype.card (SupportedEdgeState K) ∧
        (states i).edgeState = (states j).edgeState ∧
        (∀ n,
          i ≤ n →
          n < j →
          (states (n + 1)).v = (states n).transition.z0 ∧
          (states (n + 1)).x = (states n).transition.z1) ∧
        ∀ n,
          i ≤ n →
          n < j →
          (states (n + 1)).edgeState ≠
            (states n).edgeState) :
    (∃ m : Move23Site,
      m.LegalIn K) ∨
      ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K') := by
  classical
  by_contra hnone

  have hNoMove23 :
      ¬ ∃ m : Move23Site,
        m.LegalIn K := by
    intro hmove23
    exact hnone (Or.inl hmove23)

  have hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K') := by
    intro hdescent
    exact hnone (Or.inr hdescent)

  obtain ⟨states, _hstart, hstep, hconsecutive⟩ :=
    hcore.exists_perpetual_highFanState_of_noMove23_noDescent_noHigh
      hM
      hlinks
      hNoFour
      hNoMove23
      hNoDescent
      hNoHigh
      start

  obtain
      ⟨i, j, hgap, hbound, hreturn, hstepSegment, hconsecutiveSegment⟩ :=
    exists_recurrent_highFanEdgeState states hstep hconsecutive

  exact hNoCycle
    ⟨states, i, j, hgap, hbound, hreturn, hstepSegment, hconsecutiveSegment⟩


/-- A repeated retained local fan location with the same transverse carrier
also fixes both chord endpoints. -/
theorem FanChordTransition.same_location_same_transverse_same_chord
    {K : Triangulation} {v x : Nat}
    (T0 T1 : FanChordTransition K v x)
    (hcore : ClosedTriangulationCore K)
    (hσ : T0.sigma.1 = T1.sigma.1)
    (hρ : T0.rho.1 = T1.rho.1)
    (htrans : T0.transverse = T1.transverse) :
    T0.z0 = T1.z0 ∧ T0.z1 = T1.z1 := by
  have hexhaust :
      ∀ (σ : LinkTriangle) (a b c : Nat),
        σ.verts.Nodup →
        a ∈ σ.verts →
        b ∈ σ.verts →
        c ∈ σ.verts →
        a ≠ b → a ≠ c → b ≠ c →
        ∀ q, q ∈ σ.verts → q = a ∨ q = b ∨ q = c := by
    intro σ a b c hnodup ha hb hc hab hac hbc q hq
    rcases σ with ⟨s0, s1, s2⟩
    simp [LinkTriangle.verts] at hnodup ha hb hc hq ⊢
    aesop

  have hσmem : T0.sigma.1 ∈ vertexLinkTriangles K v := by
    exact
      (mem_vertexLinkStarTriangles_iff K v x T0.sigma.1).1
        T0.sigma.2 |>.1
  have hρmem : T0.rho.1 ∈ vertexLinkTriangles K v := by
    exact
      (mem_vertexLinkStarTriangles_iff K v x T0.rho.1).1
        T0.rho.2 |>.1
  have hσnodup : T0.sigma.1.verts.Nodup :=
    vertexLinkTriangles_triangle_nodup K hcore v T0.sigma.1 hσmem
  have hρnodup : T0.rho.1.verts.Nodup :=
    vertexLinkTriangles_triangle_nodup K hcore v T0.rho.1 hρmem

  have hxσ : x ∈ T0.sigma.1.verts :=
    ((mem_vertexLinkStarTriangles_iff K v x T0.sigma.1).1
      T0.sigma.2).2
  have hxρ : x ∈ T0.rho.1.verts :=
    ((mem_vertexLinkStarTriangles_iff K v x T0.rho.1).1
      T0.rho.2).2

  have htransσ : T0.transverse ∈ T0.sigma.1.verts := by
    have hv : T0.transverse ≠ v := by
      intro h
      have hd := T0.distinct
      exact (List.nodup_cons.mp hd).1 (by simp [h])
    exact
      (T0.leftTet.mem_linkTriangleAt?_iff
        v T0.transverse T0.sigma.1 T0.leftTet_link hv).2
        ((T0.leftTet_match T0.transverse).2
          (by simp [Tet.verts]))
  have htransρ : T0.transverse ∈ T0.rho.1.verts := by
    have hv : T0.transverse ≠ v := by
      intro h
      have hd := T0.distinct
      exact (List.nodup_cons.mp hd).1 (by simp [h])
    exact
      (T0.rightTet.mem_linkTriangleAt?_iff
        v T0.transverse T0.rho.1 T0.rightTet_link hv).2
        ((T0.rightTet_match T0.transverse).2
          (by simp [Tet.verts]))

  have hz0σ0 : T0.z0 ∈ T0.sigma.1.verts := by
    have hv : T0.z0 ≠ v := by
      intro h
      have hd := T0.distinct
      exact (List.nodup_cons.mp hd).1 (by simp [h])
    exact
      (T0.leftTet.mem_linkTriangleAt?_iff
        v T0.z0 T0.sigma.1 T0.leftTet_link hv).2
        ((T0.leftTet_match T0.z0).2
          (by simp [Tet.verts]))
  have hz0σ1 : T1.z0 ∈ T0.sigma.1.verts := by
    have hv : T1.z0 ≠ v := by
      intro h
      have hd := T1.distinct
      exact (List.nodup_cons.mp hd).1 (by simp [h])
    have hz :
        T1.z0 ∈ T1.sigma.1.verts := by
      exact
        (T1.leftTet.mem_linkTriangleAt?_iff
          v T1.z0 T1.sigma.1 T1.leftTet_link hv).2
          ((T1.leftTet_match T1.z0).2
            (by simp [Tet.verts]))
    simpa [hσ] using hz

  have hx_trans : x ≠ T0.transverse := by
    intro h
    simpa [h] using T0.distinct
  have hx_z0 : x ≠ T0.z0 := by
    intro h
    simpa [h] using T0.distinct
  have htrans_z0 : T0.transverse ≠ T0.z0 := by
    intro h
    simpa [h] using T0.distinct
  have hz0'_x : T1.z0 ≠ x := by
    intro h
    simpa [h] using T1.distinct
  have hz0'_trans : T1.z0 ≠ T0.transverse := by
    intro h
    simpa [h, htrans] using T1.distinct

  have hz0eq : T0.z0 = T1.z0 := by
    rcases
        hexhaust T0.sigma.1 x T0.transverse T0.z0
          hσnodup hxσ htransσ hz0σ0
          hx_trans hx_z0 htrans_z0 T1.z0 hz0σ1 with
      h | h | h
    · exact (hz0'_x h).elim
    · exact (hz0'_trans h).elim
    · exact h.symm

  have hz1ρ0 : T0.z1 ∈ T0.rho.1.verts := by
    have hv : T0.z1 ≠ v := by
      intro h
      have hd := T0.distinct
      exact (List.nodup_cons.mp hd).1 (by simp [h])
    exact
      (T0.rightTet.mem_linkTriangleAt?_iff
        v T0.z1 T0.rho.1 T0.rightTet_link hv).2
        ((T0.rightTet_match T0.z1).2
          (by simp [Tet.verts]))
  have hz1ρ1 : T1.z1 ∈ T0.rho.1.verts := by
    have hv : T1.z1 ≠ v := by
      intro h
      have hd := T1.distinct
      exact (List.nodup_cons.mp hd).1 (by simp [h])
    have hz :
        T1.z1 ∈ T1.rho.1.verts := by
      exact
        (T1.rightTet.mem_linkTriangleAt?_iff
          v T1.z1 T1.rho.1 T1.rightTet_link hv).2
          ((T1.rightTet_match T1.z1).2
            (by simp [Tet.verts]))
    simpa [hρ] using hz

  have hx_z1 : x ≠ T0.z1 := by
    intro h
    simpa [h] using T0.distinct
  have htrans_z1 : T0.transverse ≠ T0.z1 := by
    intro h
    simpa [h] using T0.distinct
  have hz1'_x : T1.z1 ≠ x := by
    intro h
    simpa [h] using T1.distinct
  have hz1'_trans : T1.z1 ≠ T0.transverse := by
    intro h
    simpa [h, htrans] using T1.distinct

  have hz1eq : T0.z1 = T1.z1 := by
    rcases
        hexhaust T0.rho.1 x T0.transverse T0.z1
          hρnodup hxρ htransρ hz1ρ0
          hx_trans hx_z1 htrans_z1 T1.z1 hz1ρ1 with
      h | h | h
    · exact (hz1'_x h).elim
    · exact (hz1'_trans h).elim
    · exact h.symm

  exact ⟨hz0eq, hz1eq⟩

end Poincare
