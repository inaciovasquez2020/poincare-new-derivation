import Poincare.GlobalHighEdgeToFanState

namespace Poincare

/-- Endpoint-preserving form of high-edge reinjection.  The existing theorem
returns only `Nonempty (HighFanState K)`, but its construction is centered on
the represented edge `(p,q)`.  Retaining those endpoint equalities is needed
by the linked mixed fan/reentry dynamics. -/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_highFanState_on_edge_of_edgeIncidence_four_le
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
      ∃ state : HighFanState K,
        state.v = p ∧ state.x = q := by
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

    let state : HighFanState K :=
      {
        v := p
        x := q
        v_supported := hpSupport
        x_supported := hqSupport
        endpoints_ne := hpq
        transition := T
      }

    exact Or.inr ⟨state, rfl, rfl⟩

end Poincare
