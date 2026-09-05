import Poincare.TriangulationTopologicalFourSimplexRealizationChange
import Poincare.TriangulationTopologicalS3
import Poincare.TriangulationTopologicalHomeomorphTransport

namespace Poincare

/-- A closed, overlap-connected zero-defect triangulation has genuine
topology-bearing realization homeomorphic to the unit three-sphere. -/
theorem ClosedTriangulationCore.realizationHomeomorphicToThreeSphere_of_PhiSupport_eq_zero
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    (hconn : TetrahedronVertexOverlapConnected K)
    {tau : Tet}
    (htauK : tau ∈ K.tets)
    (htau : tau.verts.Nodup) :
    TriangulationRealizationHomeomorphicToThreeSphere K := by
  obtain ⟨hfront⟩ :=
    hcore.nonempty_homeomorph_fourSimplexFrontier hPhi hconn htauK htau
  exact ⟨hfront.trans fourSimplexFrontierHomeomorphUnitSphere⟩

/-- The normalized form of genuine three-sphere recognition. -/
theorem ClosedTriangulationCore.realizationHomeomorphicToThreeSphere_of_normalized
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hnorm : normalized K)
    (hconn : TetrahedronVertexOverlapConnected K)
    {tau : Tet}
    (htauK : tau ∈ K.tets)
    (htau : tau.verts.Nodup) :
    TriangulationRealizationHomeomorphicToThreeSphere K := by
  exact hcore.realizationHomeomorphicToThreeSphere_of_PhiSupport_eq_zero
    hnorm hconn htauK htau

end Poincare
