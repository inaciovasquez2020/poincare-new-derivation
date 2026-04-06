import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

def step (T : Triangulation) : Triangulation :=
  applyMove T (selectMove T)

theorem step_strict :
  ∀ T : Triangulation, Phi T > 0 → Phi (step T) < Phi T := by
  intro T h
  sorry

end Poincare
