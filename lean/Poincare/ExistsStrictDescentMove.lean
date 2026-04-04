import Mathlib
import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

axiom exists_strict_descent_move :
  ∀ T : Triangulation,
    Phi T ≠ 0 →
    ∃ m : PachnerMove,
      Phi (applyMove T m) < Phi T

end Poincare
