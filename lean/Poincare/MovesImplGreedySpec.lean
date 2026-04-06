import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy

namespace Poincare

theorem selectMoveImplGreedy_spec :
  ∀ K : Triangulation, Phi K > 0 →
    Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K := by
  intro K hPhi
  sorry

end Poincare
