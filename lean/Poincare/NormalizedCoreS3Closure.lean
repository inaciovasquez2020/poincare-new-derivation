import Poincare.TriangulationTopologicalNormalizedS3

namespace Poincare

/--
A closed, overlap-connected normalized triangulation has a
topology-bearing realization homeomorphic to the three-sphere.

The tetrahedron nondegeneracy hypothesis is discharged internally by
ClosedTriangulationCore.
-/
theorem ClosedTriangulationCore.realizationHomeomorphicToThreeSphere_of_normalized_core
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hnorm : normalized K)
    (hconn : TetrahedronVertexOverlapConnected K) :
    TriangulationRealizationHomeomorphicToThreeSphere K := by
  obtain ⟨tau, htauK⟩ := hconn.1
  exact hcore.realizationHomeomorphicToThreeSphere_of_normalized
    hnorm hconn htauK (hcore.1 tau htauK)

end Poincare
