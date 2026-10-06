import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy

namespace Poincare

/-
BOUNDARY := ¬ ∀ (K : Triangulation),
  Phi K > 0 →
  Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K

The current implementation is identity:
  applyMoveImpl K m = K.
Therefore the strict descent statement is inconsistent whenever Phi K > 0.
A genuine site-based move implementation and a proved descent theorem are required.
-/

end Poincare
