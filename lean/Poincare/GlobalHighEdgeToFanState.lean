import Poincare.GlobalFanChordEdgeProgress

namespace Poincare

/-- A represented edge of incidence at least four can be re-entered into the
high-fan dynamics without assuming that high edges are absent.  Its ambient
cyclic fan has an adjacent pair; that pair either exposes a legal `2-3` move
or produces a `FanChordTransition` and hence a new `HighFanState`.

The incidence-three output of the adjacent-pair classifier is impossible
because the input edge already has incidence at least four. -/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_highFanState_of_edgeIncidence_four_le
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {p q : Nat}
    (hpq : p ≠ q)
    {sigma : Tet}
    (hsigma : sigma ∈ K.tets)
    (hpSigma : p ∈ sigma.verts)
    (hqSigma : q ∈ sigma.verts)
    (hinc :
      4 ≤ (K.tets.filter
        (fun gamma => p ∈ gamma.verts ∧ q ∈ gamma.verts)).length) :
    (∃ m : Move23Site, m.LegalIn K) ∨
      Nonempty (HighFanState K) := by
  have hpos :
      0 < (K.tets.filter
        (fun gamma => p ∈ gamma.verts ∧ q ∈ gamma.verts)).length := by
    omega

  have hrep : VertexLinkVertexRepresented K p q :=
    hcore.vertexLinkVertexRepresented_of_edgeIncidence_pos
      p q hpq hpos

  obtain ⟨F⟩ :=
    hcore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold hM hrep

  obtain ⟨alpha, beta, hadj⟩ := F.exists_adjacent

  rcases
      hcore.ambientEdgeCyclicFan_adjacent_transition hM F hadj with
    hmove23 | hthree | htransition

  · exact Or.inl hmove23

  · have : False := by
      omega
    exact this.elim

  · obtain ⟨T⟩ := htransition

    have hpSupport : p ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      exact List.mem_flatMap.2 ⟨sigma, hsigma, hpSigma⟩

    have hqSupport : q ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      exact List.mem_flatMap.2 ⟨sigma, hsigma, hqSigma⟩

    exact
      Or.inr
        ⟨{
          v := p
          x := q
          v_supported := hpSupport
          x_supported := hqSupport
          endpoints_ne := hpq
          transition := T
        }⟩

/-- A fan-chord transition can be continued without excluding the
source-obstruction high-edge alternative.  If the chord has incidence three
and produces a represented Move32 source-face obstruction, the certified
source edge of incidence at least four is converted back into a `HighFanState`.
The ordinary high-incidence chord branch is packaged as a `HighFanState` as
well.

Thus `hNoHigh` is not needed for this one-step continuation.  No claim is made
here that the returned high-fan state has a central edge distinct from the
original `v-x` edge in every branch. -/
theorem
    ClosedTriangulationCore.FanChordTransition.continue_recycleHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    {v x : Nat}
    (T : FanChordTransition K v x) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    Nonempty (HighFanState K) := by
  rcases
      ClosedTriangulationCore.FanChordTransition.continue
        hcore hM hNoFour T with
    hmove23 | hdescent | hobstruction | hnext

  · exact Or.inl hmove23

  · exact Or.inr (Or.inl hdescent)

  · obtain ⟨s, _hsd, _hse, hrealized, _hthree, hsource⟩ := hobstruction

    obtain ⟨p, q, sigma, hpq, hsigma, hpSigma, hqSigma,
        _hnonself, hinc⟩ :=
      hcore.exists_nonself_sourceEdge_high_of_move32_sourceFace_obstruction_of_no_degree_four
        hlinks hNoFour s hrealized hsource

    have hinc' :
        4 ≤ (K.tets.filter
          (fun gamma => p ∈ gamma.verts ∧ q ∈ gamma.verts)).length := by
      simpa using hinc

    rcases
        hcore.exists_legal_move23_or_highFanState_of_edgeIncidence_four_le
          hM hpq hsigma hpSigma hqSigma hinc' with
      hlegal | hfan

    · exact Or.inl hlegal

    · exact Or.inr (Or.inr hfan)

  · obtain ⟨T'⟩ := hnext

    exact
      Or.inr
        (Or.inr
          ⟨{
            v := T.z0
            x := T.z1
            v_supported := T.z0_supported
            x_supported := T.z1_supported
            endpoints_ne := T.endpoints_ne
            transition := T'
          }⟩)

end Poincare
