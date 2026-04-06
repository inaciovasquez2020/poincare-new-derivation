import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy
import Poincare.GreedySelectorCorrect

namespace Poincare

theorem selectMoveImplGreedy_spec :
  ∀ K : Triangulation, Phi K > 0 →
    Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K := by
  intro K hPhi
  rcases greedy_selector_correct K hPhi with ⟨m, hm_eq, hm_drop⟩
  simpa [hm_eq] using hm_drop

end Poincare
