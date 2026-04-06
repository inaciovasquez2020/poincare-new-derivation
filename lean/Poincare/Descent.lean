import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

axiom step_strict :
  ∀ K, Phi K > 0 →
    ∃ m : PachnerMove, Phi (applyMove K m) < Phi K

end Poincare
