import Poincare.TriangulationTopologicalGeometricCompactness
import Poincare.TriangulationTopologicalGeometricHausdorff
import Poincare.TriangulationTopologicalHonestManifold

open Set
open scoped Manifold

namespace Poincare

/--
For the canonical realization, compactness and Hausdorffness are already
theorems.  Thus the genuine closed connected topological three-manifold
hypothesis has exactly three remaining witnesses: compatible
three-dimensional charts, the corresponding `IsManifold` structure, and
connectedness.
-/
theorem
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_iff_manifold_connected
    (K : Triangulation) :
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K ↔
      ∃ _ : ChartedSpace ThreeManifoldModel
          (triangulationTopologicalGeometricCarrier K),
        ∃ _ : IsManifold (𝓡 3) 0
            (triangulationTopologicalGeometricCarrier K),
          IsConnected
            (Set.univ : Set (triangulationTopologicalGeometricCarrier K)) := by
  constructor
  · rintro ⟨_, _, _, _, hconnected⟩
    exact ⟨inferInstance, inferInstance, hconnected⟩
  · rintro ⟨hcharted, hmanifold, hconnected⟩
    letI := hcharted
    letI := hmanifold
    exact ⟨inferInstance, inferInstance, inferInstance,
      triangulationTopologicalGeometricCarrier_univ_isCompact K,
      hconnected⟩

end Poincare
