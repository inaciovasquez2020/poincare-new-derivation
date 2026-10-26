import Poincare.TriangulationTopologicalNormalizedS3

namespace Poincare

/--
Unconditional Poincare target for the repository's topology-bearing
triangulation realization.

This is the target proposition, not a proof. It deliberately contains no
global-descent hypothesis: every closed-core realization that is an honest
closed, connected, simply connected topological three-manifold must be
homeomorphic to the unit three-sphere.
-/
def PoincareConjectureTarget : Prop :=
  ∀ K : Triangulation,
    ClosedTriangulationCore K →
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K →
    TriangulationRealizationSimplyConnected K →
    TriangulationRealizationHomeomorphicToThreeSphere K

/--
The current conditional theorem discharges the target if the separate global
strict-descent proposition is supplied. This wrapper records the reduction
without promoting that proposition to an established theorem.
-/
theorem poincareConjectureTarget_of_global_PhiSupport_descent
    (hdescent : SimplyConnectedGlobalPhiSupportDescent) :
    PoincareConjectureTarget := by
  intro K hcore hM hSC
  exact conditional_poincare_of_simplyConnected_global_PhiSupport_descent
    hdescent hcore hM hSC

/--
Open frontier: an unconditional proof of this target is not provided here.
Do not replace this declaration with an axiom or an admitted proof; either
would make the formal status misleading.
-/
end Poincare
