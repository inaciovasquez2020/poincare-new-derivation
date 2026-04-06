import Poincare.Triangulation
import Poincare.Moves
import Poincare.Descent

namespace Poincare

theorem exists_strict_descent_move :
  ∀ T : Triangulation,
    Phi T ≠ 0 →
    ∃ m : PachnerMove, Phi (applyMove T m) < Phi T := by
  intro T hne
  have hpos : Phi T > 0 := Nat.pos_of_ne_zero hne
  exact step_strict T hpos

end Poincare
