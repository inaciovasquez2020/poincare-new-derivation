import Poincare.Moves
import Poincare.MovesImpl
import Poincare.Triangulation

namespace Poincare

axiom happly_impl : applyMove = applyMoveImpl
axiom hselect_impl : selectMove = selectMoveImpl
axiom selectMoveImpl_spec :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMoveImpl K (selectMoveImpl K)) < Phi K

end Poincare
