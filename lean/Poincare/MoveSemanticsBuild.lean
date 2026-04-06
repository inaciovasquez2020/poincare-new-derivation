import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.ExistsStrictDescentMove

namespace Poincare

theorem move_semantics_strict_drop
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K := by
  exact exists_strict_descent_move K hPhi

end Poincare
