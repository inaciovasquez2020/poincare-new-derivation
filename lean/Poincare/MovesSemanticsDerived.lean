import Poincare.MovesSemantics
import Poincare.MovesSwap
import Poincare.MovesSwapSelect

namespace Poincare

theorem applyMove_spec_derived :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_from_impl

theorem selectMove_spec_derived :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K :=
  selectMove_spec_from_impl

end Poincare
