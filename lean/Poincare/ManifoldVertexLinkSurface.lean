import Poincare.TriangulationTopologicalManifoldConnectedLinkClosedCore

namespace Poincare

/--
An honest closed connected topological three-manifold
has a connected closed-surface certificate at every
represented vertex.

This does not establish that the link is S².
-/
theorem vertexLinkConnectedClosedSurfaceCertificate_of_topologicalThreeManifold
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v : Nat}
    (hv : v ∈ vertexSupport K) :
    VertexLinkConnectedClosedSurfaceCertificate K v := by
  exact
    connectedLinkClosedCore_vertexLinks_connectedClosedSurfaceCertificate
      K
      (connectedLinkClosedCore_of_topologicalThreeManifold K hcore hM)
      (vertexLinksLocallyConnected_of_topologicalThreeManifold K hcore hM)
      (by
        intro u hu x hrep
        exact hcore.vertexLinkStarDegreeTwo hrep)
      v hv

end Poincare
