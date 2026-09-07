import Poincare.TriangulationTopologicalManifoldVertexLinkStarConnectedness

namespace Poincare

/-- An honest topological three-manifold triangulation has a closed core with
connected combinatorial vertex links at every supported vertex. -/
theorem connectedLinkClosedCore_of_topologicalThreeManifold
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K) :
    ConnectedLinkClosedCore K := by
  refine ⟨hcore, ?_⟩
  intro v hv
  exact vertexLinkConnected_of_topologicalThreeManifold K hcore hM hv

end Poincare
