import Poincare.Moves
import Poincare.MovesImpl
import Poincare.MovesSemantics
import Poincare.MovesClosure

namespace Poincare

axiom happly_impl : applyMove = applyMoveImpl
axiom hselect_impl : selectMove = selectMoveImpl

theorem applyMove_spec_from_impl :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K :=
  abstract_applyMove_from_impl happly_impl

end Poincare
