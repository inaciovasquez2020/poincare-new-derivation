import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy
import Poincare.GreedySelectorCorrect

namespace Poincare

theorem exists_strict_descent_move
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K := by
  refine ⟨selectMoveImplGreedy K, ?_⟩
  exact greedy_selector_correct K hPhi

end Poincare
