import Poincare.MoveSemanticsBuild

namespace Poincare

theorem defect_balance_implies_step_strict :
  ∀ K : Triangulation, Phi K > 0 →
    ∃ m : PachnerMove, Phi (applyMove K m) < Phi K :=
  step_strict_constructive

end Poincare
