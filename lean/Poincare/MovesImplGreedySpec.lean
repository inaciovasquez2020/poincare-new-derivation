import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy

namespace Poincare

axiom selectMoveImplGreedy_spec :
  ∀ K : Triangulation, Phi K > 0 →
    Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K

end Poincare
