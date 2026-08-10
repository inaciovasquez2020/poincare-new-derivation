import Poincare.TriangulationTopologicalGeometricConnectedness
import Poincare.TriangulationTopologicalManifoldReduction

namespace Poincare

/--
When the represented tetrahedra are connected through shared vertex labels,
the only remaining content of the honest closed connected Hausdorff
three-manifold hypothesis is the existence of three-dimensional local charts.
-/
theorem
    triangulationRealizationClosedConnectedHausdorffThreeManifold_iff_charted_of_overlapConnected
    (K : Triangulation) (hK : TetrahedronVertexOverlapConnected K) :
    TriangulationRealizationClosedConnectedHausdorffThreeManifold K ↔
      Nonempty
        (ChartedSpace ThreeManifoldModel
          (triangulationTopologicalGeometricCarrier K)) := by
  rw [
    triangulationRealizationClosedConnectedHausdorffThreeManifold_iff_charted_connected
  ]
  constructor
  · rintro ⟨hcharted, _⟩
    exact ⟨hcharted⟩
  · rintro ⟨hcharted⟩
    exact ⟨hcharted,
      triangulationTopologicalGeometricCarrier_univ_isConnected K hK⟩

end Poincare
