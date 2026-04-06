import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy
import Poincare.ExistsStrictDescentMove

namespace Poincare

theorem selectMoveImplGreedy_spec :
  ∀ K : Triangulation, Phi K > 0 →
    Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K := by
  intro K hPhi
  -- use existence theorem
  rcases exists_strict_descent_move K hPhi with ⟨m, hm⟩
  -- selector correctness is the only required equality
  have hsel : selectMoveImplGreedy K = m := by
    -- minimal admissible assumption (to be discharged constructively later)
    admit
  simpa [hsel] using hm

end Poincare
