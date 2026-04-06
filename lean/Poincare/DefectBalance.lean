import Poincare.Triangulation
import Poincare.Moves
import Poincare.Step
import Poincare.AxiomFrontier

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
  · unfold vertexDefect vertexDegree
    rw [applyMove_spec_available K (selectMove K)]
  · intro u hu
    unfold vertexDefect vertexDegree
    rw [applyMove_spec_available K (selectMove K)]

end Poincare
