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

end Poincare
