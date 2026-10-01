import Poincare.TriangulationTopologicalHonestConnectedness
import Poincare.NormalizedCoreS3Closure

namespace Poincare

/--
An honest closed connected topological 3-manifold realization whose
combinatorial core is normalized is genuinely homeomorphic to S³.

The overlap-connectedness hypothesis is derived from the connected
realization rather than assumed separately.
-/
theorem ClosedTriangulationCore.realizationHomeomorphicToThreeSphere_of_normalized_honestManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hnorm : normalized K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K) :
    TriangulationRealizationHomeomorphicToThreeSphere K := by
  have hconn :
      TetrahedronVertexOverlapConnected K :=
    hcore.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold hM
  exact hcore.realizationHomeomorphicToThreeSphere_of_normalized_core
    hnorm hconn

end Poincare
