import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.ExistsStrictDescentMove

namespace Poincare

noncomputable def solveStep (K : Triangulation) : Triangulation :=
  if h : Phi K = 0 then
    K
  else
    let m := Classical.choose (exists_strict_descent_move K (Nat.pos_of_ne_zero h))
    applyMoveImpl K m

theorem solveStep_eq_self_of_phi_zero
  (K : Triangulation)
  (h0 : Phi K = 0) :
  solveStep K = K := by
  simp [solveStep, h0]

theorem solveStep_strict_drop
  (K : Triangulation)
  (hpos : Phi K > 0) :
  Phi (solveStep K) < Phi K := by
  have hne : Phi K ≠ 0 := Nat.ne_of_gt hpos
  simp [solveStep, hne]
  exact Classical.choose_spec (exists_strict_descent_move K hpos)

theorem solveStep_preserves_zero
  (K : Triangulation)
  (h0 : Phi K = 0) :
  Phi (solveStep K) = 0 := by
  simp [solveStep, h0]

end Poincare
