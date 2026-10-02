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
          cases hav
          cases hab
          have hσ : as = bs := Subtype.ext has
          have hρ : ar = br := Subtype.ext har
          cases hσ
          cases hρ
          rfl
    exact location_ext q.location r.location hv hx hs hr

end Poincare
