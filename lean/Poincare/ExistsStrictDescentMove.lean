import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy
import Poincare.GreedySelectorCorrect

namespace Poincare

/-
BOUNDARY := ¬ ∀ (K : Triangulation),
  Phi K > 0 →
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K

The current applyMoveImpl is the identity, so a strict descent move cannot
be obtained from the present implementation.
-/

end Poincare
