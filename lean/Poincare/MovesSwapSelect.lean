import Poincare.Moves
import Poincare.MovesImpl
import Poincare.MovesClosure
import Poincare.Triangulation

namespace Poincare

axiom happly_impl : applyMove = applyMoveImpl
axiom hselect_impl : selectMove = selectMoveImpl
axiom selectMoveImpl_spec :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMoveImpl K (selectMoveImpl K)) < Phi K

theorem selectMove_spec_from_impl :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K := by
  intro K hK
  rw [happly_impl, hselect_impl]
  exact selectMoveImpl_spec K hK

end Poincare
