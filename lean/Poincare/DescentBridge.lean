import Poincare.Descent
import Poincare.MoveSemanticsBuild

namespace Poincare

theorem step_strict_constructive_bridge :
  ∀ K : Triangulation, Phi K > 0 →
    ∃ m : PachnerMove, Phi (applyMove K m) < Phi K :=
  step_strict_constructive

end Poincare
