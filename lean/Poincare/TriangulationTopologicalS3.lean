import Mathlib.Analysis.InnerProductSpace.PiL2
import Poincare.TriangulationTopologicalSimplyConnected

namespace Poincare

/-- The standard ambient Euclidean four-space whose unit sphere is `S³`. -/
abbrev ThreeSphereAmbient :=
  EuclideanSpace ℝ (Fin 4)

/--
Genuine recognition of the topology-bearing triangulation realization as the
three-sphere.  This is deliberately distinct from the legacy numerical
predicate `S3` on `Triangulation`.
-/
def TriangulationRealizationHomeomorphicToThreeSphere
    (K : Triangulation) : Prop :=
  Nonempty
    (triangulationTopologicalGeometricCarrier K ≃ₜ
      ↥(Metric.sphere (0 : ThreeSphereAmbient) 1))

/-- Exact expansion of genuine three-sphere recognition. -/
theorem triangulationRealizationHomeomorphicToThreeSphere_iff
    (K : Triangulation) :
    TriangulationRealizationHomeomorphicToThreeSphere K ↔
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :=
  Iff.rfl

end Poincare
