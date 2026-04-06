import Poincare.Triangulation
import Poincare.MovesImpl

namespace Poincare

axiom exists_strict_descent_move
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K

end Poincare
