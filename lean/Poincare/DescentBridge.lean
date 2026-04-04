import Poincare.Descent
import Poincare.DefectBalance

namespace Poincare

axiom defect_balance_implies_step_strict :
  (∀ (K : Triangulation) (v : Nat),
    pivotVertex K = some v →
    let K' := step K
    vertexDefect K' v < vertexDefect K v ∧
    ∀ u : Nat, u ≠ v → vertexDefect K' u ≤ vertexDefect K u) →
  ∀ K, Phi K > 0 → Phi (step K) < Phi K

end Poincare
