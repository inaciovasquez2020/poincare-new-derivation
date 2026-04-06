import Poincare.Triangulation
import Poincare.Moves
import Poincare.Step
import Poincare.MovesSemantics

namespace Poincare

theorem applyMove_defect_balance
  (K : Triangulation)
  (v : Nat)
  (hK : pivotVertex K = some v) :
  let K' := step K
  vertexDefect K' v = vertexDefect K v ∧
  ∀ u : Nat, u ≠ v → vertexDefect K' u = vertexDefect K u := by
  dsimp [step]
  constructor
  · rfl
  · intro u hu
    rfl

end Poincare
