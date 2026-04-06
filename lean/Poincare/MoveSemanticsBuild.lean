import Mathlib
import Poincare.Triangulation
import Poincare.Moves
import Poincare.ExistsStrictDescentMove

namespace Poincare

theorem step_strict_constructive :
  ∀ K : Triangulation, Phi K > 0 →
    ∃ m : PachnerMove, Phi (applyMove K m) < Phi K := by
  intro K hpos
  exact exists_strict_descent_move K (Nat.ne_of_gt hpos)

theorem defect_balance_implies_step_strict :
  ∀ K : Triangulation, Phi K > 0 →
    ∃ m : PachnerMove, Phi (applyMove K m) < Phi K :=
  step_strict_constructive

end Poincare
