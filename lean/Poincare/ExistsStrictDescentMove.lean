import Poincare.Triangulation
import Poincare.Moves
import Poincare.MovesSemantics

namespace Poincare

theorem exists_strict_descent_move :
  ∀ T : Triangulation,
    Phi T ≠ 0 →
    Phi (applyMove T (selectMove T)) < Phi T := by
  intro T hne
  have hpos : Phi T > 0 := Nat.pos_of_ne_zero hne
  simpa using selectMove_spec T hpos

end Poincare
