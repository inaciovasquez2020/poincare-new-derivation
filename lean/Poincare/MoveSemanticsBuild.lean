import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.ExistsStrictDescentMove

namespace Poincare

/-
BOUNDARY := ¬ ∀ (K : Triangulation),
  Phi K > 0 →
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K

The imported strict-descent theorem was removed because applyMoveImpl is
currently the identity.
-/

end Poincare
