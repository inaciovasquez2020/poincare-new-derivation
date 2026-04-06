import Poincare.MovesAssumptions
import Poincare.MovesClosure

namespace Poincare

theorem applyMove_spec_from_impl :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K :=
  abstract_applyMove_from_impl happly_impl

end Poincare
