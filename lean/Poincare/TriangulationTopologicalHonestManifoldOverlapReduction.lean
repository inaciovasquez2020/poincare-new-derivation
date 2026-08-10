import Poincare.TriangulationTopologicalGeometricConnectedness
import Poincare.TriangulationTopologicalHonestManifoldReduction

open Set
open scoped Manifold

namespace Poincare

/--
When the represented tetrahedra are connected through shared vertex labels,
the genuine closed connected topological three-manifold hypothesis reduces
exactly to the remaining local manifold structure: compatible
three-dimensional charts and their `IsManifold` witness.
-/
theorem
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_iff_manifold_of_overlapConnected
    (K : Triangulation) (hK : TetrahedronVertexOverlapConnected K) :
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K ↔
      ∃ _ : ChartedSpace ThreeManifoldModel
          (triangulationTopologicalGeometricCarrier K),
        Nonempty
          (IsManifold (𝓡 3) 0
            (triangulationTopologicalGeometricCarrier K)) := by
  rw [
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_iff_manifold_connected
  ]
  constructor
  · rintro ⟨hcharted, hmanifold, _⟩
    exact ⟨hcharted, ⟨hmanifold⟩⟩
  · rintro ⟨hcharted, ⟨hmanifold⟩⟩
    exact ⟨hcharted, hmanifold,
      triangulationTopologicalGeometricCarrier_univ_isConnected K hK⟩

end Poincare
