import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.ExistsStrictDescentMove

namespace Poincare

/-
BOUNDARY := solveStep cannot currently be defined from
exists_strict_descent_move because the strict-descent theorem is unavailable.
-/

/-
noncomputable def solveStep (K : Triangulation) : Triangulation := ...
-/

theorem solveStep_eq_self_of_phi_zero
  (K : Triangulation)
  (h0 : Phi K = 0) :
  solveStep K = K := by
  sorry

theorem solveStep_strict_drop
  (K : Triangulation)
  (hpos : Phi K > 0) :
  Phi (solveStep K) < Phi K := by
  sorry

theorem solveStep_preserves_zero
  (K : Triangulation)
  (h0 : Phi K = 0) :
  Phi (solveStep K) = 0 := by
  sorry

end Poincare
