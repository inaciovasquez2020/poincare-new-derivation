import Poincare.GlobalFanChordMove2332SecondStep
import Poincare.TriangulationTopologicalManifoldConnectedLinkClosedCore

namespace Poincare

/-- The legal `2-3,3-2` prefix preserves enough honest-manifold structure to
recover the repository's connected-link closed-core package on its output. -/
theorem Move23Site.first_move32_prefix_connectedLinkClosedCore
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlegal : m.LegalIn K)
    (hslegal : s.LegalIn (m.replace K)) :
    ConnectedLinkClosedCore (s.replace (m.replace K)) := by
  have hcore1 : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hcore2 : ClosedTriangulationCore (s.replace (m.replace K)) :=
    hcore1.move32Site_replace_closedCore s hslegal
  have hM2 :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold
        (s.replace (m.replace K)) :=
    (m.first_move32_prefix_topological_package
      s hcore hM hlegal hslegal).1
  exact connectedLinkClosedCore_of_topologicalThreeManifold
    (s.replace (m.replace K)) hcore2 hM2

end Poincare
