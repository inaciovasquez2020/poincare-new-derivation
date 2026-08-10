import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Poincare.TriangulationTopologicalManifold

open Set
open scoped Manifold

namespace Poincare

/--
The genuine closed connected Hausdorff topological three-manifold hypothesis
on the canonical realization, stated with Mathlib's actual manifold
predicate.  The `IsManifold (𝓡 3) 0` witness records compatibility of the
three-dimensional Euclidean charts at topological regularity.
-/
def TriangulationRealizationIsClosedConnectedTopologicalThreeManifold
    (K : Triangulation) : Prop :=
  ∃ _ : T2Space (triangulationTopologicalGeometricCarrier K),
    ∃ _ : ChartedSpace ThreeManifoldModel
        (triangulationTopologicalGeometricCarrier K),
      ∃ _ : IsManifold (𝓡 3) 0
          (triangulationTopologicalGeometricCarrier K),
        IsCompact
            (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) ∧
          IsConnected
            (Set.univ : Set (triangulationTopologicalGeometricCarrier K))

/-- Exact expansion of the genuine topological three-manifold hypothesis. -/
theorem
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_iff
    (K : Triangulation) :
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K ↔
      ∃ _ : T2Space (triangulationTopologicalGeometricCarrier K),
        ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
            (triangulationTopologicalGeometricCarrier K),
          ∃ _ : IsManifold (𝓡 3) 0
              (triangulationTopologicalGeometricCarrier K),
            IsCompact
                (Set.univ :
                  Set (triangulationTopologicalGeometricCarrier K)) ∧
              IsConnected
                (Set.univ :
                  Set (triangulationTopologicalGeometricCarrier K)) :=
  Iff.rfl

end Poincare
