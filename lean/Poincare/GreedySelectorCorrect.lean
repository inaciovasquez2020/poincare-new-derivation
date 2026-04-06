import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy

namespace Poincare

axiom greedy_selector_correct :
  ∀ (K : Triangulation),
    Phi K > 0 →
    Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K

end Poincare
