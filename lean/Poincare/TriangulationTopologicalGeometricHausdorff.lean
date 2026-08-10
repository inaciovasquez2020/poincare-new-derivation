import Mathlib.Topology.Separation.Hausdorff
import Poincare.TriangulationTopologicalSimplyConnected

namespace Poincare

/--
The canonical topology-bearing realization is Hausdorff, as a subspace of the
Hausdorff Pi-space `Nat → ℝ`.
-/
noncomputable instance triangulationTopologicalGeometricCarrier.instT2Space
    (K : Triangulation) :
    T2Space (triangulationTopologicalGeometricCarrier K) := by
  unfold triangulationTopologicalGeometricCarrier
  change @T2Space
    ↥(triangulationTopologicalGeometricComplex K).space
    instTopologicalSpaceSubtype
  infer_instance

end Poincare
