import Poincare.Triangulation
import Poincare.SolveStepBuild

namespace Poincare

theorem program_closure_zero_or_drop
  (T : Triangulation) :
  Phi T = 0 ∨ Phi (solveStep T) < Phi T := by
  classical
  by_cases h0 : Phi T = 0
  · exact Or.inl h0
  · have hpos : Phi T > 0 := Nat.pos_of_ne_zero h0
    exact Or.inr (solveStep_strict_drop T hpos)

end Poincare
