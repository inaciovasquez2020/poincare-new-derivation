import Poincare.Moves
import Poincare.MovesSemantics
import Poincare.MovesSemanticsDerived

namespace Poincare

theorem applyMove_spec_available :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_derived

theorem selectMove_spec_available :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K :=
  selectMove_spec_derived

end Poincare
