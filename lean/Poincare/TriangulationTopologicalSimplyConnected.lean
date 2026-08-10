import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Instances.Real.Lemmas
import Poincare.TriangulationTopologicalGeometricCarrier

namespace Poincare

/-- The realization subtype carries the topology induced from the Pi-space. -/
noncomputable instance triangulationTopologicalGeometricCarrier.instTopologicalSpace
    (K : Triangulation) :
    TopologicalSpace (triangulationTopologicalGeometricCarrier K) := by
  unfold triangulationTopologicalGeometricCarrier
  infer_instance

/--
Genuine simple-connectedness of the topology-bearing geometric realization.
This is Mathlib's `SimplyConnectedSpace` on the realization subtype, not the
legacy combinatorial placeholder `simply_connected`.
-/
def TriangulationRealizationSimplyConnected (K : Triangulation) : Prop :=
  SimplyConnectedSpace (triangulationTopologicalGeometricCarrier K)

/--
The realization predicate is exactly Mathlib's simple-connectedness predicate
for the corresponding subset of the ambient Pi-space.
-/
theorem triangulationRealizationSimplyConnected_iff_isSimplyConnected_space
    (K : Triangulation) :
    TriangulationRealizationSimplyConnected K ↔
      IsSimplyConnected (triangulationTopologicalGeometricComplex K).space :=
  Iff.rfl

end Poincare
