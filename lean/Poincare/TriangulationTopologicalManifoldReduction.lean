import Poincare.TriangulationTopologicalGeometricCompactness
import Poincare.TriangulationTopologicalGeometricHausdorff
import Poincare.TriangulationTopologicalManifold

open Set

namespace Poincare

/--
For the canonical realization, compactness and Hausdorffness are already
theorems.  Thus the honest closed connected Hausdorff topological
three-manifold hypothesis has exactly two remaining obligations: a
three-dimensional charted-space structure and connectedness.
--/
theorem
    triangulationRealizationClosedConnectedHausdorffThreeManifold_iff_charted_connected
    (K : Triangulation) :
    TriangulationRealizationClosedConnectedHausdorffThreeManifold K ↔
      ∃ _ : ChartedSpace ThreeManifoldModel
          (triangulationTopologicalGeometricCarrier K),
        IsConnected
          (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) := by
  constructor
  · rintro ⟨_, _, _, hconnected⟩
    exact ⟨inferInstance, hconnected⟩
  · rintro ⟨hcharted, hconnected⟩
    letI := hcharted
    exact ⟨inferInstance, inferInstance,
      triangulationTopologicalGeometricCarrier_univ_isCompact K,
      hconnected⟩

end Poincare
