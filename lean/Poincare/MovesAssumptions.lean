import Poincare.Moves
import Poincare.MovesImpl
import Poincare.MovesImplGreedy
import Poincare.MovesImplGreedySpec
import Poincare.Triangulation

namespace Poincare

theorem happly_impl : applyMove = applyMoveImpl := rfl
theorem hselect_impl : selectMove = selectMoveImplGreedy := rfl

/-
BOUNDARY := ¬ ∀ K : Triangulation, Phi K > 0 →
  Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K

The imported greedy implementation is currently identity-based, so no strict
descent theorem can be derived from it.
-/

end Poincare
