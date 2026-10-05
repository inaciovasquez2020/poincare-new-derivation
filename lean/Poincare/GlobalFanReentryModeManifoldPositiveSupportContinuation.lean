import Poincare.GlobalFanReentryModePositiveSupportContinuation
import Poincare.TriangulationTopologicalManifoldConnectedLinkClosedCore
import Poincare.TriangulationTopologicalHonestConnectedness

namespace Poincare

/-- Honest three-manifoldness supplies the connected-link and tetrahedron-overlap
hypotheses needed by positive-support fan/reentry continuation.  Thus no
independent combinatorial connectivity assumptions remain at the call site. -/
theorem ClosedTriangulationCore.exists_legal_move23_or_descent_or_next_fanReentryMode_of_topologicalThreeManifold_PhiSupport_pos
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
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
  have hconnected : ConnectedLinkClosedCore K :=
    connectedLinkClosedCore_of_topologicalThreeManifold K hcore hM
  have hconn : TetrahedronVertexOverlapConnected K :=
    hcore.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold hM
  exact
    hcore.exists_legal_move23_or_descent_or_next_fanReentryMode_of_PhiSupport_pos
      hM hconnected.2 hconn hphi q

end Poincare
