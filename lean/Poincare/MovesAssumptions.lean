import Poincare.Moves
import Poincare.MovesImpl
import Poincare.MovesImplGreedy
import Poincare.MovesImplGreedySpec
import Poincare.Triangulation

namespace Poincare

theorem happly_impl : applyMove = applyMoveImpl := rfl
theorem hselect_impl : selectMove = selectMoveImplGreedy := rfl

theorem selectMoveImpl_spec :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K :=
  selectMoveImplGreedy_spec

end Poincare
