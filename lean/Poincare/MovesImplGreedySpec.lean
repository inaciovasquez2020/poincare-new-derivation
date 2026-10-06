import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy

namespace Poincare

/-
BOUNDARY := ¬ ∀ K : Triangulation, Phi K > 0 →
  Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K

The current applyMoveImpl is the identity, so this strict descent theorem
cannot hold for positive Phi.
-/

end Poincare
