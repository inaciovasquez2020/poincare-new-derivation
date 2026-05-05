import Poincare.Triangulation
import Poincare.Moves
import Poincare.MovesImpl

namespace Poincare

/--
Repository obstruction:
`applyMoveImpl` is currently the identity map.
-/
theorem applyMoveImpl_identity
    (K : Triangulation) (m : PachnerMove) :
    applyMoveImpl K m = K := by
  rfl

/--
Therefore no strict-descent theorem using the current `applyMoveImpl`
can be repository-internal unless `Phi K < Phi K` is allowed.
-/
theorem current_applyMoveImpl_blocks_strict_descent
    (K : Triangulation) (m : PachnerMove) :
    ¬ Phi (applyMoveImpl K m) < Phi K := by
  simp [applyMoveImpl]

end Poincare
