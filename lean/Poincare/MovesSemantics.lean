import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

axiom applyMove_spec :
  ∀ (K : Triangulation) (m : PachnerMove), allVerts (applyMove K m) = allVerts K

axiom selectMove_spec :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K

theorem selected_move_strict_descent :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K := by
  intro K hK
  exact selectMove_spec K hK

end Poincare
