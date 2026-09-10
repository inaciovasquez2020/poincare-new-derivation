import Poincare.GlobalMove32SourceFaceHighEdgeAvoidance
import Poincare.GlobalHighEdgeToFanStateWithEndpoints

namespace Poincare

/-- A represented source-face obstruction can be reinjected as a high-fan
state while retaining avoidance of any prescribed old edge.  The only other
outcome is an immediately legal `2-3` move.

The returned high-fan edge is also nonself relative to the obstructed
Move32 site's incidence-three shared edge. -/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_highFanState_away_from_edge_of_move32_sourceFace_obstruction_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ theta ∈ K.tets,
        s.a ∈ theta.verts ∧
        s.b ∈ theta.verts ∧
        s.c ∈ theta.verts)
    (v x : Nat)
    (hvx : v ≠ x) :
    (∃ m : Move23Site, m.LegalIn K) ∨
      ∃ next : HighFanState K,
        canonicalEdgeKey next.v next.x ≠ canonicalEdgeKey v x ∧
        ¬ ((next.v = s.d ∧ next.x = s.e) ∨
           (next.v = s.e ∧ next.x = s.d)) := by
  obtain
      ⟨p, q, theta,
        hpq, htheta, hp, hq,
        haway, hnonself, hinc⟩ :=
    hcore.exists_high_sourceEdge_away_from_edge_of_move32_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour s hrealized hobstruction v x hvx

  rcases
      hcore.exists_legal_move23_or_highFanState_on_edge_of_edgeIncidence_four_le
        hM hpq htheta hp hq hinc with
    hmove23 | hstate

  · exact Or.inl hmove23

  · obtain ⟨next, hv, hx⟩ := hstate

    have haway' :
        canonicalEdgeKey next.v next.x ≠ canonicalEdgeKey v x := by
      rw [hv, hx]
      exact haway

    have hnonself' :
        ¬ ((next.v = s.d ∧ next.x = s.e) ∨
           (next.v = s.e ∧ next.x = s.d)) := by
      intro hself
      rw [hv, hx] at hself
      exact hnonself hself

    exact Or.inr ⟨next, haway', hnonself'⟩

end Poincare
