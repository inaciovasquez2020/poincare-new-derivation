import Poincare.GlobalDegreeFourDescent
import Poincare.GlobalFanReentryModeContinuation

namespace Poincare

/-- Positive support defect removes the no-degree-four side condition from the
fan/reentry mode continuation.  A supported degree-four vertex gives strict
topology-preserving `PhiSupport` descent immediately; otherwise the existing
fan/reentry continuation theorem applies unchanged. -/
theorem ClosedTriangulationCore.exists_legal_move23_or_descent_or_next_fanReentryMode_of_PhiSupport_pos
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hphi : 0 < PhiSupport K)
    (q : FanReentryModeState K) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    Nonempty (FanReentryModeState K) := by
  rcases
      hcore.exists_topology_preserving_PhiSupport_descent_or_no_degree_four
        hlinks hconn hphi with
    hdescent | hNoFour
  · exact Or.inr (Or.inl hdescent)
  · exact
      hcore.exists_legal_move23_or_descent_or_next_fanReentryMode
        hM hlinks hconn hNoFour q

end Poincare
