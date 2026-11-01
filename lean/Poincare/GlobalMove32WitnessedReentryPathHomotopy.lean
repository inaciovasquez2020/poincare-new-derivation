import Poincare.GlobalMove32ReentryPolygonalLoop
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace Poincare

/-- A witnessed reentry arc is endpoint-relative homotopic to an arc obtained
from the same exact tetrahedral witness relation by the canonical constructor.
This supplies a global path-homotopy correspondence, not a support-controlled
homotopy or a simplicial chain equivalence. -/
theorem WitnessedReentryTransitionArc.exists_path_homotopic_witness_arc
    {K : Triangulation}
    (hSC : TriangulationRealizationSimplyConnected K)
    (s t : Move32Site)
    (hs : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s t)
    (actual : WitnessedReentryTransitionArc K s t hs) :
    ∃ canonical : WitnessedReentryTransitionArc K s t hs,
      actual.path.Homotopic canonical.path := by
  letI : SimplyConnectedSpace (triangulationTopologicalGeometricCarrier K) := hSC
  obtain ⟨canonical⟩ := witnessedReentry_transitionArc s t hs hstep
  exact ⟨canonical,
    SimplyConnectedSpace.paths_homotopic actual.path canonical.path⟩

end Poincare
