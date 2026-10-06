import Poincare.MovesSemantics
import Poincare.MovesSwap
import Poincare.MovesSwapSelect

namespace Poincare

theorem applyMove_spec_derived :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_from_impl

/-- BOUNDARY: strict descent is not available from the current implementation. -/

end Poincare
