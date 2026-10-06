import Poincare.AxiomFrontier

namespace Poincare

theorem applyMove_spec :
  ∀ (K : Triangulation) (m : PachnerMove), allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_available

end Poincare
