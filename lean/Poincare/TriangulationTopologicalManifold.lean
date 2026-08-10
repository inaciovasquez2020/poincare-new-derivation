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

/--
The honest closed connected Hausdorff topological three-manifold hypothesis
on the canonical realization.  `ChartedSpace` supplies the local Euclidean
three-dimensional charts, `T2Space` supplies the Hausdorff separation axiom,
and compactness and connectedness state the remaining global conditions.

This is kept distinct from
`TriangulationRealizationClosedConnectedThreeManifold`, which does not include
the Hausdorff hypothesis.
-/
def TriangulationRealizationClosedConnectedHausdorffThreeManifold
    (K : Triangulation) : Prop :=
  ∃ _ : T2Space (triangulationTopologicalGeometricCarrier K),
    ∃ _ : ChartedSpace ThreeManifoldModel
        (triangulationTopologicalGeometricCarrier K),
      IsCompact
          (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) ∧
        IsConnected
          (Set.univ : Set (triangulationTopologicalGeometricCarrier K))

/-- Exact expansion of the honest Hausdorff closed connected three-manifold
hypothesis. -/
theorem triangulationRealizationClosedConnectedHausdorffThreeManifold_iff
    (K : Triangulation) :
    TriangulationRealizationClosedConnectedHausdorffThreeManifold K ↔
      ∃ _ : T2Space (triangulationTopologicalGeometricCarrier K),
        ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
            (triangulationTopologicalGeometricCarrier K),
          IsCompact
              (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) ∧
            IsConnected
              (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) :=
  Iff.rfl

end Poincare
