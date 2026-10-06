import Poincare.AxiomFrontier

namespace Poincare

theorem applyMove_spec :
  ∀ (K : Triangulation) (m : PachnerMove), allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_available

/-- BOUNDARY: selected-move strict descent is not available from the current implementation. -/

end Poincare
