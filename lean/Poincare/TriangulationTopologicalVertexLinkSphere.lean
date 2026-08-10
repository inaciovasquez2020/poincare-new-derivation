import Poincare.TriangulationTopologicalVertexLinkRealizationChange

namespace Poincare

/--
Zero vertex defect gives a genuine two-sphere link in the topology-bearing
Pi-space realization, provided the represented link vertices have the local
degree-two property needed by the certified tetrahedral-boundary argument.
-/
noncomputable def
    vertexLinkPiRealizationHomeomorphUnitSphereOfVertexDefectZero
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (hzero : vertexDefect K v = 0)
    (hdeg :
      ∀ x : Nat,
        VertexLinkVertexRepresented K v x →
          VertexLinkStarDegreeTwo K v x) :
    ↥(triangulationTopologicalVertexLink K v) ≃ₜ
      ↥(Metric.sphere (0 : TetrahedronAmbient) 1) :=
  vertexLinkPiRealizationHomeomorphUnitSphere K hcore v
    (vertexLinkTetrahedralBoundaryCertificate_of_vertexDefect_zero
      K hcore v hzero hdeg)

end Poincare
