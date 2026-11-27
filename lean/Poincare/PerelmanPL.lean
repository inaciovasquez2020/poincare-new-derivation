import Poincare.TriangulationTopologicalNormalizedS3
import Poincare.CrossPolytopeBoundary

namespace Poincare

/-- The old assertion `∀ K, S3 K` is false: `S3` is the
numerical zero-`PhiSupport` predicate, not homeomorphism to the 3-sphere.
The boundary of the four-dimensional cross-polytope is a counterexample. -/
theorem universal_S3_false :
    ¬ (∀ K : Triangulation, S3 K) := by
  intro h
  have hzero : PhiSupport crossPolytopeBoundary4 = 0 :=
    h crossPolytopeBoundary4
  exact (Nat.ne_of_gt crossPolytopeBoundary4_PhiSupport_pos) hzero

/-- The genuine, restricted topological Poincare statement, expressed as
a proposition rather than introduced as an unproved Lean axiom.
Status: CONDITIONAL_EXTERNAL_THEOREM_ONLY.

This includes the honest closed connected topological 3-manifold and
simply-connectedness hypotheses, and concludes a real homeomorphism to S³.
It does NOT imply that arbitrary triangulations have zero `PhiSupport`. -/
def Perelman_PL : Prop :=
  ∀ K : Triangulation,
    ClosedTriangulationCore K →
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K →
    TriangulationRealizationSimplyConnected K →
    TriangulationRealizationHomeomorphicToThreeSphere K

/-- Conditional: the external theorem must be supplied as an explicit
hypothesis.  This declaration adds no axiom or proof of that hypothesis. -/
theorem conditional_PL_poincare_recognition
    (hPL : Perelman_PL)
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hSC : TriangulationRealizationSimplyConnected K) :
    TriangulationRealizationHomeomorphicToThreeSphere K :=
  hPL K hcore hM hSC

/-- The repository's existing induction proves this conditional bridge.
Its `SimplyConnectedGlobalPhiSupportDescent` premise remains unproved. -/
theorem globalPhiSupportDescent_implies_Perelman_PL
    (hdescent : SimplyConnectedGlobalPhiSupportDescent) :
    Perelman_PL := by
  intro K hcore hM hSC
  exact conditional_poincare_of_simplyConnected_global_PhiSupport_descent
    hdescent hcore hM hSC

end Poincare
