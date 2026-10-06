import Poincare.MovesSwap
import Poincare.MovesSwapSelect

namespace Poincare

theorem applyMove_spec_derived_nocycle :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_from_impl

end Poincare
