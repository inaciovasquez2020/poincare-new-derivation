import Poincare.Moves
import Poincare.Descent
import Poincare.PhiPosOfNeZero

namespace Poincare

theorem exists_strict_descent_move :
∀ T : Triangulation,
Phi T ≠ 0 →
∃ m : PachnerMove, Phi (applyMove T m) < Phi T := by
intro T hT
have hpos : 0 < Phi T := phi_pos_of_ne_zero T hT
refine ⟨selectMove T, ?_⟩
simpa [step] using step_strict T hpos

end Poincare
