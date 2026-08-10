import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Poincare.TriangulationTopologicalSimplyConnected

open Set

namespace Poincare

/-- The Euclidean local model for a topological three-manifold. -/
abbrev ThreeManifoldModel := EuclideanSpace ℝ (Fin 3)

/--
The honest closed connected topological three-manifold hypothesis on the
canonical realization.  The charted-space witness supplies Euclidean
three-dimensional local charts; compactness is the topological meaning of
closed here, and connectedness is stated independently of simple-connectedness.
-/
def TriangulationRealizationClosedConnectedThreeManifold
    (K : Triangulation) : Prop :=
  ∃ _ : ChartedSpace ThreeManifoldModel
      (triangulationTopologicalGeometricCarrier K),
    IsCompact
        (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) ∧
      IsConnected
        (Set.univ : Set (triangulationTopologicalGeometricCarrier K))

/-- Exact expansion of the genuine closed connected three-manifold hypothesis. -/
theorem triangulationRealizationClosedConnectedThreeManifold_iff
    (K : Triangulation) :
    TriangulationRealizationClosedConnectedThreeManifold K ↔
      ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
          (triangulationTopologicalGeometricCarrier K),
        IsCompact
            (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) ∧
          IsConnected
            (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) :=
  Iff.rfl

end Poincare
