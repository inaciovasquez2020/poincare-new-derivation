import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy

namespace Poincare

axiom greedy_selector_correct :
  ∀ (K : Triangulation),
    Phi K > 0 →
    ∃ m : PachnerMove,
      m = selectMoveImplGreedy K ∧
      Phi (applyMoveImpl K m) < Phi K

end Poincare
